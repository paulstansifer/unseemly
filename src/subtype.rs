use crate::{
    ast::{
        Ast,
        AstContents::{Atom, Node, Shape, VariableReference},
    },
    ast_walk::{walk, LazyWalkReses, WalkRule},
    form::Form,
    name::{n, Name},
    ty::TypeError,
    util::assoc::Assoc,
    walk_mode::{NegativeWalkMode, WalkMode},
};

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct Subtype {}
}

// TODO: gensym and store
fn mystery_id() -> Name { n("mystery_for_typechecking") }

fn new_mystery(supers: Vec<Ast>, subs: Vec<Ast>) -> Ast {
    raw_ast!(Shape(vec![
        raw_ast!(Atom(mystery_id())),
        raw_ast!(Shape(supers)),
        raw_ast!(Shape(subs))
    ]))
}

fn unpack_mystery(mystery: Ast) -> (Vec<Ast>, Vec<Ast>) {
    let Shape(mystery_parts) = mystery.c() else { icp!() };
    let Shape(subs) = mystery_parts[2].c().clone() else {icp!() };
    let Shape(supers) = mystery_parts[1].c().clone() else {icp!() };

    (supers, subs)
}

fn complete_mystery() -> Ast { new_mystery(vec![], vec![]) }

fn constrain_mystery(mystery: Ast, constraint: Ast, super_type: bool) -> Ast {
    let (mut supers, mut subs) = unpack_mystery(mystery);

    let constraints = if super_type { &mut supers } else { &mut subs };

    if !constraints.contains(&constraint) {
        constraints.push(constraint);
    }

    new_mystery(supers, subs)
}

fn merge_mysteries(mystery_lhs: Ast, mystery_rhs: Ast) -> Ast {
    let mut lhs = unpack_mystery(mystery_lhs);
    let rhs = unpack_mystery(mystery_rhs);

    for constraint in rhs.0 {
        if !lhs.0.contains(&constraint) {
            lhs.0.push(constraint);
        }
    }

    for constraint in rhs.1 {
        if !lhs.1.contains(&constraint) {
            lhs.1.push(constraint);
        }
    }

    new_mystery(lhs.0, lhs.1)
}

// TODO: we should really have some sort of general mechanism...
// `expect_ty_node!` isn't quite right; we just want to panic if it fails
fn destr_forall(a: &Ast) -> Option<(Vec<Name>, &Ast)> {
    if let Node(f, parts, _) = a.c() {
        if f.name != n("forall_type") {
            return None;
        }
        return Some((
            parts.get_rep_leaf_or_panic(n("param")).into_iter().map(Ast::to_name).collect(),
            parts.get_leaf_or_panic(&n("body")),
        ));
    } else {
        return None;
    }
}

impl WalkMode for Subtype {
    fn name() -> &'static str { "Subtype" }

    type Elt = Ast;
    type Negated = UnusedPositiveSubtype;
    type AsPositive = UnusedPositiveSubtype;
    type AsNegative = Subtype;
    type Err = TypeError;
    type D = crate::walk_mode::Negative<Subtype>;
    type ExtraInfo = ();

    fn get_walk_rule(_f: &Form) -> WalkRule<Subtype> {
        cust_rc_box!(|part_types: LazyWalkReses<Subtype>| {
            match (destr_forall(&part_types.this_ast), destr_forall(part_types.context_elt())) {
                (None, None) => {
                    panic!("TODO")
                    // TODO: rename to .subtype
                    // Ok(f.type_compare.neg().clone())
                }
                _ => {
                    panic!("TODO")
                }
            }
        })
    }
    fn automatically_extend_env() -> bool { true }

    fn walk_var(n: Name, cnc: &LazyWalkReses<Subtype>) -> Result<Assoc<Name, Ast>, TypeError> {
        Ok(Assoc::single(n, match cnc.env.find(&n) {
            // If it's protected, stop:
            Some(t) if &VariableReference(n) == t.c() => t.clone(),
            Some(t) => crate::ty::synth_type(t, cnc.env.clone())?,
            // Or  canonicalize(t, cnc.env.clone()),  ?
            None => ast!((vr n)), // TODO why can this happen?
        }))
    }

    // Simply protect the name; don't try to unify it.
    fn underspecified(nm: Name) -> Ast { ast!((vr nm)) }

    fn neg__env_merge(
        lhs: &Assoc<Name, Ast>,
        rhs: &Assoc<Name, Ast>,
    ) -> Result<Assoc<Name, Ast>, TypeError> {
        // combine constraints
        Ok(lhs.union_with(rhs, merge_mysteries))
    }
}

impl NegativeWalkMode for Subtype {
    fn needs_pre_match() -> bool { false } // we hack `get_walk_rule` for a similar purpose
}

custom_derive! {
    #[derive(Copy, Clone, Debug, Reifiable)]
    pub struct UnusedPositiveSubtype {}
}

impl WalkMode for UnusedPositiveSubtype {
    fn name() -> &'static str { "XXXXX" }

    type Elt = Ast;
    type Negated = Subtype;
    type AsPositive = UnusedPositiveSubtype;
    type AsNegative = Subtype;
    type Err = TypeError;
    type D = crate::walk_mode::Positive<UnusedPositiveSubtype>;
    type ExtraInfo = ();

    fn get_walk_rule(_: &Form) -> WalkRule<UnusedPositiveSubtype> { icp!() }
    fn automatically_extend_env() -> bool { icp!() }
}
