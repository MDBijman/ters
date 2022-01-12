use aterms::base::parse_term_from_string;
use ters::{parse_rewrite_file, Rewriter};

fn run_e2e_test(rw_string: &str, in_term: &str, out_term: &str) {
    let r = ters::parse_rewrite_string(rw_string).unwrap();
    println!("{:#?}", r);
    let mut rw = Rewriter::new_with_prelude(r);
    let input = parse_term_from_string(in_term).unwrap();
    let result = rw.rewrite(input);
    let expected = parse_term_from_string(out_term).unwrap();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), expected);
}

#[test]
fn test_meta_ref() {
    run_e2e_test(
        "main: f -> .match[1] f;
        match[a]: _ -> a;",
        "Test()",
        "1",
    );

    run_e2e_test(
        "main: f -> .match[.id] f;
        match[.f]: t -> .f t;",
        "Test()",
        "Test()",
    );

    run_e2e_test(
        "main: f -> .apply[.do[.id]] f;
        do[.f]: a -> .apply[.f] a;
        apply[.f]: t -> .f t;",
        "Test()",
        "Test()",
    );
}

#[test]
fn test_array() {
    run_e2e_test(
        "main: f -> .is_list f;",
        "[1, 2, 3]",
        "[1, 2, 3]");

    run_e2e_test(
        "main: f -> .do_list f;
        do_list: [] -> 1;
        do_list: [h|t] -> 2;",
        "[1, 2, 3]",
        "2");
}

#[test]
fn test_meta_strategy() {
    run_e2e_test(
        "main: f -> .do[.inc] f;
        do[.f]: t -> .f t;
        inc: i -> .add (i, 1);",
        "1",
        "2",
    );
}

#[test]
fn test_nested_meta_1() {
    run_e2e_test(
        "main: f -> .do[.do[.inc]] f;
        do[.f]: t -> .f t;
        inc: i -> .add (i, 1);",
        "1",
        "2",
    );
}

#[test]
fn test_nested_meta_2() {
    run_e2e_test(
        "main: f -> .map[.do[.inc]] f;
        do[.f]: t -> .f t;
        inc: i -> .add (i, 1);",
        "[1, 2, 3]",
        "[2,3,4]",
    );
}

#[test]
fn test_nested_meta_3() {
    run_e2e_test(
        "main: f -> .env_map[.do[.inc]] ([], f);
        do[.f]: (e, t) -> (e, .f t);
        inc: i -> .add (i, 1);",
        "[1, 2, 3]",
        "([], [2,3,4])",
    );
}

#[test]
fn test_annotated_values() {
    run_e2e_test(
        "main: f -> .id f;",
        "[1 {Thing()}, 2 {Thing()}, 3 {Thing()}]",
        "[1 {Thing()}, 2 {Thing()}, 3 {Thing()}]",
    );
}

#[test]
fn test_annotation() {
    run_e2e_test(
        "main: f -> .annot f;
         annot: f -> f{Annot()};",
        "Test()",
        "Test(){Annot}",
    );
}

#[test]
fn test_meta_value() {
    run_e2e_test(
        "main: f -> .typecheck f;
        typecheck: a -> b := .map[.annotate[Thing()]] a in a;",
        "[1, 2, 3]",
        "[1 {Thing()}, 2 {Thing()}, 3 {Thing()}]",
    );
}
