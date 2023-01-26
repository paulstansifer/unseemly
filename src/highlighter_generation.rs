use crate::{earley::parse, grammar::SynEnv};

pub fn ace_rules(se: &SynEnv) -> String {
    let mut categories = vec![];
    let mut keyword_operators = vec![];
    for (_, nt_grammar) in se.iter_pairs() {
        // Separate "keyword.operator" out; there are so many of them.
        // TODO: The principled thing to do would be to do this for each name...
        let (keyword_operator, mut normal) = nt_grammar
            .textmate_categories()
            .into_iter()
            .partition(|(_, cat)| cat == "keyword.operator");
        categories.append(&mut normal);
        keyword_operators.append(&mut keyword_operator.into_iter().map(|(pat, _)| pat).collect());
    }

    keyword_operators.sort();
    keyword_operators.dedup();

    // Make one big rule for all of them (will perform better, probably):
    categories.push((keyword_operators.join("|"), "keyword.operator".to_string()));

    // Order, roughly, by specificity of syntax:
    categories.sort_by(|a, b| {
        if a.1 == "keyword" {
            return std::cmp::Ordering::Less;
        }
        if b.1 == "keyword" {
            return std::cmp::Ordering::Greater;
        }
        if a.1.starts_with("string") {
            return std::cmp::Ordering::Less;
        }
        if b.1.starts_with("string") {
            return std::cmp::Ordering::Greater;
        }
        if a.1.starts_with("paren") {
            return std::cmp::Ordering::Less;
        }
        if b.1.starts_with("paren") {
            return std::cmp::Ordering::Greater;
        }
        if a.1.starts_with("keyword.operator") {
            return std::cmp::Ordering::Less;
        }
        if b.1.starts_with("keyword.operator") {
            return std::cmp::Ordering::Greater;
        }
        if a.1.starts_with("variable") {
            return std::cmp::Ordering::Less;
        }
        if b.1.starts_with("variable") {
            return std::cmp::Ordering::Greater;
        }

        std::cmp::Ordering::Equal
    });
    categories.dedup();

    let mut res = String::new();
    for (pat, name) in categories {
        if let Ok(re) = regex::Regex::new(&pat) {
            if re.is_match("") {
                continue; // TODO: warn about regexes matching empty strings!
            }
        } else {
            continue; // TODO: warn about bad regexes!
        }
        res.push_str(&format!(
            "{{ token: '{}', regex: /{}/ }},\n",
            name,
            // Remove some regexp concepts not supported by JS:
            pat.replace(r"\p{Letter}", r"[a-zA-Z\xa1-\uFFFF]")
                .replace(r"\p{Number}", r"[0-9]")
                .replace("/", "\\/") // Escape slashes
        ))
    }
    res
}

pub fn dynamic__ace_rules(prog: &str, lang: &crate::Language) -> String {
    // This only works with the Unseemly syntax extension form, which sets this side-channel:
    crate::core_macro_forms::syn_envs__for__highlighting.with(|envs| envs.borrow_mut().clear());

    // Errors are okay, especially late!
    let _ = parse(&crate::core_forms::outermost_form(), lang.pc.clone(), prog);

    let mut result = String::new();

    crate::core_macro_forms::syn_envs__for__highlighting.with(|envs| {
        use indoc::writedoc;
        use std::fmt::Write;

        let mut prev_grammar = lang.pc.grammar.clone();
        let mut cur_rule_name = "start".to_string();
        let mut idx = 0;

        for (extender_ast, grammar) in &*envs.borrow() {
            let longest_line = extender_ast
                .orig_str(prog)
                .split('\n')
                .map(str::trim)
                .max_by(|a, b| a.len().cmp(&b.len()))
                .unwrap();

            writedoc!(
                result,
                "
                {}: [
                {{ token: 'text', regex: /(?={})/, next: 'still_{}' }}, {}
                ],
                ",
                cur_rule_name,
                regex::escape(longest_line).replace('/', "\\/"),
                cur_rule_name,
                ace_rules(&prev_grammar),
            )
            .unwrap();

            idx += 1;
            let next_rule_name = format!("lang_{}", idx);

            // Stay in the current language until we hit `in`.
            writedoc!(
                result,
                "
                still_{}: [
                {{ token: 'keyword.operator', regex: 'in', next: '{}' }}, {}
                ],
                ",
                cur_rule_name,
                next_rule_name,
                ace_rules(&prev_grammar),
            )
            .unwrap();

            cur_rule_name = next_rule_name;

            prev_grammar = grammar.clone();
        }

        writedoc!(
            result,
            "
            {}: [
            {} ],",
            cur_rule_name,
            ace_rules(&prev_grammar),
        )
        .unwrap();
    });

    result
}
