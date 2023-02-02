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

fn is_mystery(a: &Ast) -> bool {
    let Shape(shape_parts) = a.c() else { return false; };
    return !shape_parts.is_empty() && shape_parts[0].c() == &Atom(mystery_id());
}

fn unpack_mystery(mystery: &Ast) -> (Vec<Ast>, Vec<Ast>) {
    let Shape(mystery_parts) = mystery.c() else { icp!() };
    let Shape(subs) = mystery_parts[2].c().clone() else {icp!() };
    let Shape(supers) = mystery_parts[1].c().clone() else {icp!() };

    (supers, subs)
}

fn complete_mystery() -> Ast { new_mystery(vec![], vec![]) }

fn constrain_mystery(mystery: &Ast, constraint: Ast, super_type: bool) -> Ast {
    let (mut supers, mut subs) = unpack_mystery(mystery);

    let constraints = if super_type { &mut supers } else { &mut subs };

    if !constraints.contains(&constraint) {
        constraints.push(constraint);
    }

    new_mystery(supers, subs)
}

// If `ty` is a mystery, return it; otherwise, make it a fully-constrained mystery
fn ensure_mystery(ty: Ast) -> Ast {
    if is_mystery(&ty) {
        return ty;
    }
    new_mystery(vec![ty.clone()], vec![ty])
}

fn merge_mysteries(mystery_lhs: &Ast, mystery_rhs: &Ast) -> Ast {
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

fn mystery_satisfiable(mystery: &Ast, parts: &LazyWalkReses<Subtype>) -> Result<(), TypeError> {
    let (supers, subs) = unpack_mystery(mystery);

    // Pick a maximally-constrained constraint on one side;
    //  does it satisfy all the constraints on the other?
    // TODO: Does this always find a satisfaction if there is one?
    for super_constraint in &supers {
        if !supers
            .iter()
            .all(|other_super| must_subtype(super_constraint, other_super, parts).is_ok())
        {
            continue;
        }
        // all other super constraints are a supertype to this

        for sub_constriant in &subs {
            must_subtype(sub_constriant, super_constraint, parts)?
        }
    }
    Ok(())
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

fn merge_bindings(lhs: Ast, rhs: Ast) -> Ast {
    // As an optimization, if the types are spelled the same, we know they're equivalent:
    if lhs == rhs {
        return lhs;
    }

    merge_mysteries(&ensure_mystery(lhs), &ensure_mystery(rhs))
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
        // TODO: actually constrain unknowns, and ignore non-unknowns
        match cnc.env.find(&n) {
            // If it's protected, stop:
            Some(t) if &VariableReference(n) == t.c() => Ok(Assoc::new()),
            Some(t) => Ok(Assoc::single(n, crate::ty::synth_type(t, cnc.env.clone())?)),
            // Or  canonicalize(t, cnc.env.clone()),  ?
            None => ty_err!(UnboundName(n) at cnc.this_ast),
        }
    }

    // Simply protect the name; don't try to unify it.
    fn underspecified(nm: Name) -> Ast { ast!((vr nm)) }

    fn neg__env_merge(
        lhs: &Assoc<Name, Ast>,
        rhs: &Assoc<Name, Ast>,
    ) -> Result<Assoc<Name, Ast>, TypeError> {
        // combine constraints
        Ok(lhs.union_with(rhs, merge_bindings))
        // TODO: handle types with mysteries embedded in them
        // Perhaps we can just recur into them at the end?
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

pub fn must_subtype(sub: &Ast, sup: &Ast, parts: &LazyWalkReses<Subtype>) -> Result<(), TypeError> {
    if sub as *const Ast == sup as *const Ast {
        return Ok(());
    }
    if sub == sup {
        return Ok(());
    }

    let result_env = walk::<Subtype>(sup, &parts.with_context(sub.clone()))?;
    let result_parts = parts.with_environment(result_env.clone());

    for mystery in result_env.iter_values() {
        mystery_satisfiable(mystery, &result_parts)?
    }
    return Ok(());
}

pub fn must_equal(lhs: &Ast, rhs: &Ast, parts: &LazyWalkReses<Subtype>) -> Result<(), TypeError> {
    must_subtype(lhs, rhs, parts)?;
    must_subtype(rhs, lhs, parts)
}
