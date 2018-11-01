#![macro_use]

/*
 This isn't as bad as it looks.
 I mean, it's pretty bad, don't get me wrong...

 The purpose is to generate `Reifiable` `impl`s
  for any `enum` or `struct`.

 Basically, `reify` pattern-matches to destructure the actual Rust value,
  and then constructs a `Value` of the corresponding shape.

 And `reflect` does the opposite.

 But, in the process, I have to work around
  what feels like every single limitation of `macro_rules!` in Rust,
   as if I were aiming for them.

 Who wrote that piece of junk, anyway?
 */

macro_rules! Reifiable {
    // HACK: everything is parameterized over 't...


    /* struct */

    ((lifetime) $(#[$($whatever:tt)*])* $(pub)* struct $name:ident<$lifetime:tt> { $($contents:tt)* }) => {
        Reifiable!((remove_p_and_a) struct $name<$lifetime> @ { $($contents)*, } );
        // HACK: we add commas to the end of the contents, becuase it's easier to parse
        // if they end in a comma (this breaks `structs` that already have final commas...)
    };

    ((lifetime) $(#[$($whatever:tt)*])* $(pub)* struct $name:ident<$lifetime:tt $(, $ty_param_ty:ident)*> { $($contents:tt)* }) => {
        Reifiable!((remove_p_and_a) struct
            $name<$lifetime $(, $ty_param_ty)*> @ <$($ty_param_ty),*>
            { $($contents)*, } );
    };

    // no lifetime parameter
    (() $(#[$($whatever:tt)*])* $(pub)* struct $name:ident$(<$($ty_param_ty:ident),*>)* { $($contents:tt)* }) => {
        Reifiable!((remove_p_and_a) struct
            $name$(<$($ty_param_ty),*>)* @ $(<$($ty_param_ty),*>)*
            { $($contents)*, } );
    };


    // TODO: This lacks support for type-parameterized `struct`s ...

    // done! Go to `make_impl`!
    ((remove_p_and_a) $(pub)* struct $name:ident
        $(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* { $(,)* }
        $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!((make_impl) struct $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)*
            { $($($accum)*)* } );
    };

    // remove `pub`
    ((remove_p_and_a) $(pub)* struct $name:ident
        $(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* {
        pub $($contents:tt)*
    } $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!((remove_p_and_a) struct $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)* {
            $( $contents )*
        } $( [ $($accum)* ] )* );
    };

    // remove attributes (such as `///`!)
    ((remove_p_and_a) $(pub)* struct $name:ident
        $(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* {
        #[$($whatever:tt)*] $($contents:tt)*
    } $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!((remove_p_and_a) struct $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)* {
            $( $contents )*
        } $( [ $($accum)* ] )*);
    };


    // no `pub` or attr this time
    ((remove_p_and_a) $(pub)* struct $name:ident
        $(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* {
        $field_car:ident : $t_car:ty, $($cdr:tt)*
    } $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!((remove_p_and_a) struct $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)* {
            $( $cdr )*
        } [ $field_car : $t_car $(, $($accum)* )* ]);
    };


    ((make_impl) struct $name:ident
         $(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)*
         { $( $field:ident : $t:ty),* }) => {
        impl<'t $($(, $ty_param_ty : ::runtime::reify::Reifiable)*)*>
                ::runtime::reify::Reifiable
                for $name<$($($ty_param),*)*> {
            fn ty() -> ::ast::Ast {
                type_defn_wrapper!($(<$($ty_param_ty),*>)* => { "Type" "struct" :
                   "component_name" => [@"c" $(
                       (, ::ast::Ast::Atom(::name::n(stringify!($field)))) ),* ],
                   "component" =>
                   // TODO: unless we specify arguments with the same name as parameters,
                   //  we get bogus results
                   // (we get
                   //   ∀ K V. μ Assoc. struct{ n: Option<[AssocNode<[ident rust_usize]<]< }
                   //  rather than
                   //   ∀ K V. μ Assoc. struct{ n: Option<[AssocNode<[K V]<]< }
                   [@"c" $( (, <$t as ::runtime::reify::Reifiable>::ty_invocation() ) ),*]
                })
            }

            fn ty_name() -> ::name::Name { ::name::n(stringify!($name)) }

            fn ty_invocation() -> ::ast::Ast {
                // HACK: at runtime, check to see if we need type parameters by making a vector
                let argument_list : Vec<&str> = vec![$( $( stringify!($ty_param_ty) ),* )*];
                if argument_list.len() > 0 {
                    ast!({ "Type" "type_apply" :
                        "type_rator" => (, ::ast::Ast::VariableReference( Self::ty_name() ) ),
                        "arg" => [ $( $( (, $ty_param_ty ::ty_invocation() ) ),* )* ]
                    })
                } else {
                    ::ast::Ast::VariableReference( Self::ty_name() )
                }
            }

            fn reify(&self) -> ::runtime::eval::Value {
                ::runtime::eval::Struct(assoc_n!(
                    $( (stringify!($field)) => self.$field.reify()),* ))
            }

            #[allow(unused_variables)]
            fn reflect(v: &::runtime::eval::Value) -> Self {
                extract!((v) ::runtime::eval::Struct = (ref env) =>
                    $name {
                        $( $field :
                            <$t as ::runtime::reify::Reifiable>::reflect(
                                env.find(&::name::n(stringify!($field))).unwrap())),*
                    })
            }
        }
    };
    /* enum */

    // `lifetime` means that we need to pull off a lifetime argument.
    // The whole set of type parameters comes after `name`;
    //  we make a just-the-types type parameters after the @.
    ((lifetime) $(#[$($whatever:tt)*])* $(pub)* enum $name:ident<$lifetime:tt> { $( $contents:tt )* }) => {
        Reifiable!((remove_attr) enum $name<$lifetime> @ { $( $contents )* , });
    };

    ((lifetime) $(#[$($whatever:tt)*])* $(pub)* enum $name:ident<$lifetime:tt $(, $ty_param_ty:ident)*> {
        $( $contents:tt )*
    }) => {
        Reifiable!((remove_attr) enum $name<$lifetime $(, $ty_param_ty)*> @ <$($ty_param_ty),*> {
            $( $contents )* ,
        });
    };

    (() $(#[$($whatever:tt)*])* $(pub)* enum $name:ident$(<$($ty_param_ty:ident),*>)* { $( $contents:tt )* }) => {
        Reifiable!((remove_attr) enum $name$(<$($ty_param_ty),*>)* @ $(<$($ty_param_ty),*>),* {
            $( $contents )* ,
        });
    };

    // done! (has to go first)
    ((remove_attr) enum $name:ident$(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* { $(,)* }
    $([ $($accum:tt)* ])*) => {
        Reifiable!((make_impl) enum $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)*
            { $($( $accum )*)* } );
    };
    // drop the attribute
    ((remove_attr) enum $name:ident$(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* {
        #[ $($whatever:tt)* ] $( $contents:tt )*
    } $([ $($accum:tt)* ])* ) => {
        Reifiable!((remove_attr) enum $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)* {
            $( $contents )*
        } $([ $($accum)* ])* );
    };
    // no attribute this time
    ((remove_attr) enum $name:ident$(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* {
         $choice:ident$(( $($part:ty),* ))*, $( $contents:tt )*
    } $([ $($accum:tt)* ])*) => {
        Reifiable!((remove_attr) enum $name$(<$($ty_param),*>)* @ $(<$($ty_param_ty),*>)* {
            $( $contents )*
        } [ $choice $(( $($part),* ))* , $($($accum)*)* ]);
    };


    // The `$((...))*` and `$(<...>)*` patterns deal with the fact that the `()` and `<>`
    //  might be completely absent (the `*` matches 0 or 1 times)
    // The second set of type parameters are those that are not lifetime params...
    ((make_impl) enum $name:ident$(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* {
        $($choice:ident$(( $($part:ty),* ))* ,)*
    }) => {
        impl<'t $($(, $ty_param_ty : ::runtime::reify::Reifiable)*)*>
                ::runtime::reify::Reifiable
                for $name<$($($ty_param),*)*> {

            fn ty() -> ::ast::Ast {
                type_defn_wrapper!($(<$($ty_param_ty),*>)* => { "Type" "enum" :
                    "name" => [@"c" $(
                        (, ::ast::Ast::Atom(::name::n(stringify!($choice)))) ),* ],
                    "component" => [@"c" $( [ $($(
                        (, <$part as ::runtime::reify::Reifiable>::ty_invocation() )
                    ),*)*]),*]
                })
            }

            fn ty_name() -> ::name::Name { ::name::n(stringify!($name)) }

            fn ty_invocation() -> ::ast::Ast {
                // HACK: at runtime, check to see if we need type parameters by making a vector
                let argument_list : Vec<&str> = vec![$( $( stringify!($ty_param_ty) ),* )*];
                if argument_list.len() > 0 {
                    ast!({ "Type" "type_apply" :
                        "type_rator" => (, ::ast::Ast::VariableReference( Self::ty_name() ) ),
                        "arg" => [ $( $( (, $ty_param_ty ::ty_invocation() ) ),* )* ]
                    })
                } else {
                    ::ast::Ast::VariableReference( Self::ty_name() )
                }
            }

            #[allow(unused_mut)] // rustc bug! `v` has to be mutable, but it complains
            fn reify(&self) -> ::runtime::eval::Value {
                match *self { $(
                    choice_pat!( ( $($($part),*)* ) (a b c d e f g h i j k l m n o p q r s t)
                                 $name::$choice ; ())
                    => {
                        let mut v = vec![];
                        choice_vec!( ( $($($part),*)* ) (a b c d e f g h i j k l m n o p q r s t)
                                     v);
                        ::runtime::eval::Value::Enum(::name::n(stringify!($choice)), v)
                    }
                ),* }
            }

            #[allow(unused_variables)]
            fn reflect(v: &::runtime::eval::Value) -> Self {
                extract!((v) ::runtime::eval::Enum = (ref choice, ref parts) => {
                    make_enum_reflect!(choice; parts; $name$(<$($ty_param),*>)*/**/
                        { $($choice $(( $($part),* ))*),* } )
                })
            }
        }
    }
}


/* makes a pattern matching an enum with _n_ components, using the first _n_
   of the input names (be sure to supply enough names!) */
macro_rules! choice_pat {
    ( ($t_car:ty $(, $t_cdr:ty)* ) ($i_car:ident $($i_cdr:ident)*)
      $choice:path; ($($accum:ident),*)) => {
          choice_pat!( ($($t_cdr),* ) ($($i_cdr)*) $choice; ($i_car $(, $accum)*))
    };

    ( ( ) ($($i_cdr:ident)*) $choice:path; ( ) ) => {
        $choice
    };

    ( ( ) ($($i_cdr:ident)*) $choice:path; ( $($accum:ident),+ ) ) => {
        $choice($(ref $accum),*)
    };
}

macro_rules! choice_vec {
    /* the types are ignored, except for how many of them there are */
    ( ($t_car:ty $(, $t_cdr:ty)*) ($i_car:ident $($i_cdr:ident)*) $v:expr) => { {
        choice_vec!( ($($t_cdr),*)  ($($i_cdr)*) $v);
        $v.push($i_car.reify());
    } };
    ( ( ) ($($i_cdr:ident)*) $v:expr) => { {} }
}

// workaround for MBE limitation; need to walk choices, but *not* ty_param,
//  so we use this to manually walk over the choices
macro_rules! make_enum_reflect {
    ($choice_name:ident; $parts_name:ident; $name:ident$(<$($ty_param:tt),*>)*/**/ {
        $choice_car:ident $(( $($part_cars:ty),* ))*
        $(, $choice_cdr:ident$(( $($part_cdr:ty),* ))*)*
    }) => {
        if $choice_name.is(stringify!($choice_car)) {
            unpack_parts!( $(( $($part_cars),* ))* $parts_name; 0;
                           $name::$choice_car$(::< $($ty_param),* >)*; ())
        } else {
            make_enum_reflect!($choice_name; $parts_name; $name$(<$($ty_param),*>)*/**/ {
                $($choice_cdr $(( $($part_cdr),* ))* ),* })
        }
    };
    ($choice_name:ident; $parts_name:ident; $name:ident$(<$($ty_param:tt),*>)*/**/ { } ) => {
        panic!("ICE: invalid enum choice: {:#?}", $choice_name)
    }
}

macro_rules! unpack_parts {
    ( ($t_car:ty $(, $t_cdr:ty)*) $v:expr; $idx:expr; $ctor:expr; ($($accum:expr),*)) => {
        unpack_parts!( ( $($t_cdr),* ) $v; ($idx + 1); $ctor;
            ($($accum, )*
             <$t_car as ::runtime::reify::Reifiable>::reflect(& $v[$idx])))
    };
    ( () $v:expr; $idx:expr; $ctor:expr; ($($accum:expr),*)) => {
        $ctor($($accum),*)
    };
    ( $v:expr; $idx:expr; $ctor:expr; ()) => {
        $ctor // special case: a value, not a 0-arg constructor
    }
}

// For `ty`
macro_rules! type_defn_wrapper {
    ( $(<$($ty_param_ty:ident),*>)* => $body:tt ) => {
        // All types will be ∀, even if in Rust they have no parameters;
        //  this is safe, but a nuisance.
        // All types will be μ. I think this is the way things work in most languages.
        ast!({"Type" "forall_type" :
            "param" => [ $($(
                (, ::ast::Ast::Atom(::name::n(stringify!($ty_param_ty))))
            ),*)*],
            "body" => (import [* [forall "param"]] {"Type" "mu_type" :
                 "param" => [(import [prot "param"]
                              (, ::ast::Ast::VariableReference(Self::ty_name())))],
                 "body" => (import [* [prot "param"]] $body)
             })
        })
    }
}


macro_rules! refer_to_type {
    ($name:tt < $( $arg:ty ),* >) => {
        ast!({ "Type" "type_apply" :
            "type_rator" => (, ::ast::Ast::VariableReference(::name::n(stringify!($name))) ),
            "arg" => [ (, $( refer_to_type!($arg)),* )]
        })
    };
    ($name:tt) => {
        ::ast::Ast::VariableReference(::name::n(stringify!($name)))
    }
}
