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
 */

macro_rules! get_form {
    ( $nt:expr, $name:expr ) => {
        ::core_forms::find_form(&::core_forms::make_core_syn_env(), $nt, $name)
    }
}

macro_rules! Reifiable {
    // HACK: everything is parameterized over 't...


    /* struct */
    
    // TODO: This lacks support for type-parameterized `struct`s ... 
    
    // remove `pub`
    (() $(pub)* struct $name:ident$(<$($ty_param_ty:ident),*>)* { 
        pub $field_car:ident : $t_car:ty $(, $($cdr:tt)* )* /* $( $(pub)* $field_cdr:ident : $t_cdr:ty),* */ 
    } $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!(() struct $name$(<$($ty_param_ty),*>)* { $( $( $cdr )* )*
    } [ $field_car : $t_car $(, $($accum)* )* ]);
    };
    
    // no `pub` this time
    (() $(pub)* struct $name:ident$(<$($ty_param_ty:ident),*>)* { 
        $field_car:ident : $t_car:ty $(, $($cdr:tt)* )* /* $( $(pub)* $field_cdr:ident : $t_cdr:ty),* */ 
    } $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!(() struct $name$(<$($ty_param_ty),*>)* { $( $( $cdr )* )*
    } [ $field_car : $t_car $(, $($accum)* )* ]);
    };

    // done! Go to `internal`!
    (() $(pub)* struct $name:ident$(<$($ty_param_ty:ident),*>)* { 
        $(,)*
    } $( [ $( $accum:tt )* ] )* ) => {
        Reifiable!((internal) struct $name$(<$($ty_param_ty),*>)* { $($($accum)*)* } );
    };

    
    ((internal) struct $name:ident/*<'t>*/ { $( $field:ident : $t:ty),* }) => {
        impl<'t> ::runtime::reify::Reifiable<'t> for $name {
            fn ty() -> ::ast::Ast<'static> {
                ast! ({ get_form!("type", "struct") ;
                    "component_name" => [@"c" $( 
                        (, (::ast::Ast::VariableReference(n(stringify!($field))))) ),* ],
                    "component" => [@"c" $( (, (<$t as ::runtime::reify::Reifiable>::ty())) ),*]
                })
            }
            
            //fn type_name() -> Name<'static> { n(stringify!($name)) }
            
            fn reify(&self) -> ::runtime::eval::Value<'t> {
                ::runtime::eval::Struct(assoc_n!( 
                    $( (stringify!($field)) => self.$field.reify()),* ))
            }
            
            fn reflect(v: &::runtime::eval::Value<'t>) -> Self {
                extract!((v) ::runtime::eval::Struct = (ref env) => 
                    $name {
                        $( $field : 
                            <$t as ::runtime::reify::Reifiable>::reflect(
                                env.find(&n(stringify!($field))).unwrap())),*
                    })
            }
        }
    };
    /* enum */
    
    ((lifetime) $(pub)* enum $name:ident<$lifetime:tt> { 
        $($choice:ident$(( $($part:ty),* ))*),* 
    }) => {
        Reifiable!((internal) enum $name<$lifetime> @ { 
            $($choice $(( $($part),* ))*),* 
        });
    };

    ((lifetime) $(pub)* enum $name:ident<$lifetime:tt $(, $ty_param_ty:ident)*> { 
        $($choice:ident$(( $($part:ty),* ))*),* 
    }) => {
        Reifiable!((internal) enum $name<$lifetime $(, $ty_param_ty)*> @ <$($ty_param_ty),*> { 
            $($choice $(( $($part),* ))*),* 
        });
    };
    
    (() $(pub)* enum $name:ident$(<$($ty_param_ty:ident),*>)*  { 
        $($choice:ident$(( $($part:ty),* ))*),* 
    }) => {
        Reifiable!((internal) enum $name$(<$($ty_param_ty),*>)* @ $(<$($ty_param_ty),*>),* { 
            $($choice$(( $($part),* ))*),* 
        });
    };
    
    // The `$((...))*` and `$(<...>)*` patterns deal with the fact that the `()` and `<>` 
    //  might be completely absent (the `*` matches 0 or 1 times)
    // The second set of type parameters are those that are not lifetime params...
    ((internal) $(pub)* enum $name:ident$(<$($ty_param:tt),*>)* @ $(<$($ty_param_ty:ident),*>)* { 
        $($choice:ident$(( $($part:ty),* ))*),* 
    }) => {
        impl<'t $($(, $ty_param_ty : Reifiable<'t>)*)*> ::runtime::reify::Reifiable<'t> 
                for $name<$($($ty_param),*)*> {
            fn ty() -> ::ast::Ast<'static> {
                ast! ({ get_form!("type", "enum") ;
                    "name" => [@"c" $( 
                        (, (::ast::Ast::VariableReference(n(stringify!($choice))))) ),* ],
                    
                    "component" => [@"c" $( [ $($( 
                        (, (<$part as ::runtime::reify::Reifiable>::ty()) )),*)* ] ),*]
                })
            }
            
            //fn type_name() -> Name<'static> { n(stringify!($name)) }
            
            #[allow(unused_mut)] // rustc bug! `v` has to be mutable, but it complains
            fn reify(&self) -> ::runtime::eval::Value<'t> {
                match self { $(
                    choice_pat!( ( $($($part),*)* ) (a b c d e f g h i j k l m n o p q r s t) 
                                 $name::$choice ; ())
                    => {
                        let mut v = vec![];
                        choice_vec!( ( $($($part),*)* ) (a b c d e f g h i j k l m n o p q r s t) 
                                     v);
                        ::runtime::eval::Value::Enum(n(stringify!($choice)), v)
                    }
                ),* }
            }
            
            fn reflect(v: &::runtime::eval::Value<'t>) -> Self {
                extract!((v) ::runtime::eval::Enum = (ref choice, ref parts) => {
                    make_enum_reflect!(choice; parts; $name$(<$($ty_param),*>)*/*<'t>*/ 
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
        & $choice
    };

    ( ( ) ($($i_cdr:ident)*) $choice:path; ( $($accum:ident),+ ) ) => {
        & $choice($(ref $accum),*)
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
    ($choice_name:ident; $parts_name:ident; $name:ident$(<$($ty_param:tt),*>)*/*<'t>*/ { 
        $choice_car:ident $(( $($part_cars:ty),* ))* 
        $(, $choice_cdr:ident$(( $($part_cdr:ty),* ))*)* 
    }) => {    
        if $choice_name.is(stringify!($choice_car)) {
            unpack_parts!( $(( $($part_cars),* ))* $parts_name; 0; 
                           $name::$choice_car$(::< $($ty_param),* >)*; ())
        } else {
            make_enum_reflect!($choice_name; $parts_name; $name$(<$($ty_param),*>)*/*<'t>*/ {
                $($choice_cdr $(( $($part_cdr),* ))* ),* })
        }
    };
    ($choice_name:ident; $parts_name:ident; $name:ident$(<$($ty_param:tt),*>)*/*<'t>*/ { } ) => {
        panic!("ICE: invalid enum choice: {:?}", $choice_name)
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