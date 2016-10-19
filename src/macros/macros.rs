#![macro_use]

/* Assoc */

macro_rules! expr_ify {
    ($e:expr) => {$e};
}

macro_rules! assoc_n {
    () => { ::util::assoc::Assoc::new() };
    ( $k:tt => $v:expr $(, $k_cdr:tt => $v_cdr:expr)* ) => {
        assoc_n!( $( $k_cdr => $v_cdr ),* ).set(::name::n(expr_ify!($k)), $v)
    };
    ( ($k:expr) => $v:expr $(, $k_cdr:tt => $v_cdr:expr)* ) => {
        assoc_n!( $( $k_cdr => $v_cdr ),* ).set(::name::n($k), $v)
    };
}




/* Beta */

macro_rules! beta_connector {
    ( : ) => { Basic };
    ( = ) => { SameAs }
}

macro_rules! beta {
    ( [] ) => { Nothing };
    ( [* $body:tt ]) => {
        {
            let sub = beta!($body);
            let drivers = sub.names_mentioned();
            ShadowAll(Box::new(sub), drivers)
        }
    };
    ( [ $name:tt $connector:tt $t:tt
        $(, $name_cdr:tt $connector_cdr:tt $t_cdr:tt )*
         ] ) => { 
        Shadow(Box::new(beta_connector!($connector)(::name::n(expr_ify!($name)), 
                                                    ::name::n(expr_ify!($t)))),
               Box::new(beta!( [ $( $name_cdr $connector_cdr $t_cdr ),* ] )))
    }
}



/* Read */

macro_rules! tokens {
    ($($contents:tt)*) => { TokenTree{t: vec![ $(  t_elt!($contents) ),* ] }}
}

macro_rules! t_elt {
    ( [ $e:expr ;  $( $list:tt )* ] ) => { 
        Group(::name::n(concat!($e,"[")), SquareBracket, tokens!($($list)*))
    };
    ( { $e:expr ;  $( $list:tt )* } ) => { 
        Group(::name::n(concat!($e,"{")), CurlyBracket, tokens!($($list)*))
    };
    ( ( $e:expr ;  $( $list:tt )* ) ) => { 
        Group(::name::n(concat!($e,"(")), Paren, tokens!($($list)*))
    };
    ($e:expr) => { Simple(::name::n($e)) }
}



/* Ast */

macro_rules! ast_shape {
    ($($contents:tt)*) => { Shape(vec![ $(  ast!($contents) ),* ] )};
}

macro_rules! ast {
    ( (import $beta:tt $sub:tt) ) => {
        ExtendEnv(Box::new(ast!($sub)), beta!($beta))
    };
    /* // not sure we'll need this
    ( (* $env:expr => $new_env:ident / $($n:expr),* ; $($sub_args:tt)*) ) => {
        {
            let mut res = vec![];
            
            for $new_env in $env.march_all( &vec![$($n),*] ) {
                res.push(ast!($sub))
            }
            res.reverse();
            Shape(res)
        }
    };*/
    ( (vr $var:expr) ) => { ::ast::VariableReference(::name::n($var)) };
    ( (, $interp:expr)) => { $interp };
    // TODO: maybe we should use commas for consistency:
    ( ( $( $list:tt )* ) ) => { ast_shape!($($list)*)}; 
    ( { - $($mbe_arg:tt)* } ) => {
        ::ast::IncompleteNode(mbe!( $($mbe_arg)* ))
    };
    ( { $form:expr; [ $($mbe_arg:tt)* ] }) => {
        ast!( { $form ; $($mbe_arg)* } )
    };
    ( { $form:expr; $($mbe_arg:tt)* }) => {
        ::ast::Node($form, mbe!( $($mbe_arg)* ))
    };
    ($e:expr) => { ::ast::Atom(::name::n($e))}
}



/* EnvMBE*/

/* These macros generate `EnvMBE<Ast>`s, not arbitrary `EnvMBE`s, 
    which is a little un-abstract, but is the main usage. */

/*
 * Wait a second, I'm writing in Rust right now! I'll use an MBE macro to implement an MBE literal! 
 */
macro_rules! mbe_one_name {
    // `elt` ought to have an interpolation that references `new_env`
    /* TYPE PUN ALERT: $env has to be something with a `march_all` method;
        there's no trait enforcing this.
       
       But wait, isn't preventing this kind of nonsense the whole point of this project?
       
       Well, you know the old saying: 
        "While the mice are implementing the cat, the mice will play."    
    */
    ($k:tt => [* $env:expr =>($($n:expr),*) $new_env:ident : $elt:tt]) => { 
        {
            let mut v = vec![];
            let marchee = vec![$(::name::n($n)),*];
            for $new_env in $env.march_all(&marchee).into_iter() {
                v.push( mbe_one_name!($k => $elt));
            }
            ::util::mbe::EnvMBE::new_from_anon_repeat(v)            
        }
    };
    ($k:tt => [@ $n:tt $($elt:tt),*]) => {
        ::util::mbe::EnvMBE::new_from_named_repeat(
            ::name::n(expr_ify!($n)),
            vec![ $( mbe_one_name!($k => $elt) ),* ]
        )
    };
    
    ($k:tt => [$($elt:tt),*]) => {
        ::util::mbe::EnvMBE::new_from_anon_repeat(
            vec![ $( mbe_one_name!($k => $elt) ),* ])
    };
    
    // since `Ast`s go on the RHS, we have to have a distinctive interpolation syntax
    ($k:tt => (,seq $e:expr)) => { 
        {
            let mut v = vec![];
            for elt in $e { 
                v.push(::util::mbe::EnvMBE::new_from_leaves(assoc_n!($k => elt)))
            }
            ::util::mbe::EnvMBE::new_from_anon_repeat(v)
        }
    };
    
    ($k:tt => (@ $rep_n:tt ,seq $e:expr)) => { 
        {
            let mut v = vec![];
            for elt in $e { 
                v.push(::util::mbe::EnvMBE::new_from_leaves(assoc_n!($k => elt)))
            }
            ::util::mbe::EnvMBE::new_from_named_repeat(::name::n(expr_ify!($rep_n)), v)
        }
    };
    
    // For parsing reasons, we only accept expressions that are TTs.
    // It's hard to generalize the `mbe!` interface so that it accepts exprs 
    // or `[]`-surrounded trees of them.
    ($k:tt => $leaf:tt) => {
        ::util::mbe::EnvMBE::new_from_leaves(assoc_n!($k => ast!($leaf)))
    }
}


// Eventually, this ought to support more complex structures
macro_rules! mbe {
    ( $( $lhs:tt => $rhs:tt ),* ) => {{
        let single_name_mbes = vec![ $( mbe_one_name!($lhs => $rhs) ),*];
        let mut res = ::util::mbe::EnvMBE::new();
        for m in &single_name_mbes {
            res = res.merge(m);
        }
        res
    }}
}




/* FormPat */

macro_rules! form_pat {
    ((lit $e:expr)) => { Literal($e) };
    ((anyways $a:tt)) => { Anyways(ast!($a)) };
    (at) => { AnyToken };
    (aat) => { AnyAtomicToken };
    (varref) => { VarRef };
    ((delim $n:expr, $d:expr, $body:tt)) => {
        Delimited(::name::n($n), ::read::delim($d), Box::new(form_pat!($body)))
    };
    ((star $body:tt)) => {  Star(Box::new(form_pat!($body))) };
    ((alt $($body:tt),* )) => { Alt(vec![ $( form_pat!($body) ),* ] )};
    ((biased $lhs:tt, $rhs:tt)) => { Biased(Box::new(form_pat!($lhs)), 
                                            Box::new(form_pat!($rhs))) };
    ((call $n:expr)) => { Call(::name::n($n)) };
    ((scope $f:expr)) => { Scope($f) };
    ((named $n:expr, $body:tt)) => { Named(::name::n($n), Box::new(form_pat!($body))) };
    ((import $beta:tt, $body:tt)) => { 
        NameImport(Box::new(form_pat!($body)), beta!($beta))
    };
    ((extend $n:expr, $f:expr)) => {
        SynImport(::name::n($n), SyntaxExtension(Rc::new($f)))
    };
    ( [$($body:tt),*] ) => { Seq(vec![ $(form_pat!($body)),* ])}
}



/* Form */


macro_rules! basic_typed_form {
    ( $p:tt, $gen_type:expr, $eval:expr ) => {
        Rc::new(Form {
            name: ::name::n("unnamed form"),
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: ::form::Positive($gen_type),
            eval: ::form::Positive($eval)
        })
    }
}

macro_rules! typed_form {
    ( $name:expr, $p:tt, $gen_type:expr, $eval:expr ) => {
        Rc::new(Form {
            name: ::name::n($name),
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: ::form::Positive($gen_type),
            eval: ::form::Positive($eval)
        })
    }
}

macro_rules! negative_typed_form {
    ( $name:expr, $p:tt, $gen_type:expr, $eval:expr ) => {
        Rc::new(Form {
            name: ::name::n($name),
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: ::form::Negative($gen_type),
            eval: ::form::Negative($eval)
        })
    }
}

macro_rules! ambidextrous_typed_form {
    ( $name:expr, $p:tt, $gen_type:expr, $neg_gen_type:expr, $eval:expr, $neg_eval:expr) => {
        Rc::new(Form {
            name: ::name::n($name),
            grammar: form_pat!($p),
            relative_phase: Assoc::new(),
            synth_type: ::form::Both($gen_type, $neg_gen_type),
            eval: ::form::Both($eval, $neg_eval)
        })
    }
}



/* Value */

macro_rules! val {
    (i $i:expr) => { ::runtime::eval::Value::Int(::num::bigint::BigInt::from($i)) };
    (b $b:expr) => { ::runtime::eval::Value::Bool($b) };
    (cons $a:tt, $d:tt) => { ::runtime::eval::Value::Cons(Rc::new(val!($a)), Rc::new(val! $d )) };
    (f $body:tt, $params:expr, $env:tt) => {
        ::runtime::eval::Value::Function(
            Rc::new(::runtime::eval::Closure(ast!($body), $params, assoc_n! $env)))
    };
    (bif $f:expr) => { 
        ::runtime::eval::Value::BuiltInFunction(::runtime::eval::BIF(Rc::new($f))) 
    };
    (ast $nm:expr, $body:tt) => { 
        ::runtime::eval::Value::AbstractSyntax(::name::n($nm), ast! $body) 
    };
    (struct $( $k:tt => $v:tt ),* ) => { 
        ::runtime::eval::Value::Struct(assoc_n!( $( $k => val! $v),* ))
    };
    (enum $nm:expr, $($v:tt),*) => { 
        ::runtime::eval::Value::Enum(::name::n($nm), vec![ $( val! $v ),* ])
    }
}



/* core_values stuff */

macro_rules! mk_type {
    ( $se:expr, [ ( $( $param:tt ),* )  -> $ret_t:tt ] ) => {
        ast!( { find_form($se, "type", "fn") ; 
                  "param" => [ $((, mk_type!($se, $param) )),*],
                  "ret" => (, mk_type!($se, $ret_t))
        })
    };
    ( $se:expr, $n:tt ) => { ast!($n) };
}

/* Define a typed function */
macro_rules! tf {
    ( $se:expr, [ ( $($param_t:tt),* ) -> $ret_t:tt ] , 
       ( $($param_p:pat),* ) => $body:expr) => {
        TypedValue {
            ty: mk_type!($se, [ ( $($param_t),* ) -> $ret_t ] ),
            val: core_fn!( $($param_p),* => $body)
        }
    }
}

macro_rules! bind_patterns {
    ( $iter:expr; () => $body:expr ) => { $body };
    ( $iter:expr; ($p_car:pat, $($p_cdr:pat,)* ) => $body:expr ) => {
        match $iter.next() {
            Some($p_car) => {
                bind_patterns!($iter; ($( $p_cdr, )*) => $body)
            }
            None => { panic!("ICE: too few arguments"); }
            Some(ref other) => { panic!("Type ICE in argument: {:?}", other); }
        } 
    }
}

macro_rules! core_fn {
    ( $($p:pat),* => $body:expr ) => {
        BuiltInFunction(BIF(Rc::new(
            move | args | { 
                let mut argi = args.into_iter();
                bind_patterns!(argi; ($( $p, )*) => $body )
            }
        )))
    }
}




/* for core_forms */

/* Unpacking `Ast`s into environments is a pain, so here's a macro for it*/
macro_rules! expect_node {
    ( ($node:expr ; $form:expr) $env:ident ; $body:expr ) => (
        // This is tied to the signature of `Custom`
        if let Node(ref f, ref $env) = $node {
            if *f == $form { 
                $body
            } else {
               Err(())
            }
        } else {
            Err(())
        }
    )
}

// TODO: this ought to have some MBE support
macro_rules! destructure_node {
    ( ($node:expr ; $form:expr) $( $n:ident = $name:expr ),* ; $body:expr ) => (
        expect_node!( ($node ; $form) env ; {
            let ( $( $n ),* ) = ( $( env.get_leaf_or_panic(&::name::n($name)) ),* );
            $body
        })
    )
}

macro_rules! forms_to_form_pat {
    ( $( $form:expr ),* ) => {
        form_pat!((alt $( (scope $form) ),* ))
    }
}


/* panicking destructor (when the type system should offer protection) */

macro_rules! extract {
    (($v:expr) $( $expected:path = ( $( $sub:pat ),* ) => $body:expr);* ) => {
        match $v {
            $(& $expected ( $($sub),* ) => { $body } )*
            _ => { panic!("ICE: {:?} isn't a {:?}", $v, stringify!( $($expected),* )) }
        }
    }
}


