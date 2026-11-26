mod support;
use support::Case;

#[test]
fn every_stage_is_inspectable_and_ir_is_target_independent() {
    let case = Case::new(
        r#"
fn twice(x:Int)->Int{return x*2;}
fn twice(x:Str)->Str{return x+x;}
let x:=3;{let x:="a";wt twice(x);}
let chosen:=if x<5{twice(x)}else{0};
for i in 0..3{if i==1{continue;}wt chosen+i;}
"#,
    );
    for stage in ["cst", "ast", "hir", "lir", "cpp"] {
        let out = case.compile_with_options(&["--emit", stage]);
        assert!(
            out.status.success(),
            "{stage}: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let dump = std::fs::read_to_string(case.0.join("main.cpp")).unwrap();
        assert!(!dump.is_empty());
        if matches!(stage, "hir" | "lir") {
            assert!(dump.contains("function:") && dump.contains("Local("));
            assert!(
                !dump.contains("make_obj<") && !dump.contains("std::") && !dump.contains("rusk_fn")
            );
            let plain = case.compile_with_options(&["--emit", stage, "--no-opt"]);
            assert!(plain.status.success());
            assert_eq!(
                dump,
                std::fs::read_to_string(case.0.join("main.cpp")).unwrap()
            );
        }
        if stage == "hir" {
            assert!(dump.contains("If {") && dump.contains("Loop {") && dump.contains("Continue("));
        }
        if stage == "lir" {
            assert!(
                dump.contains("Branch {") && dump.contains("Jump(") && dump.contains("cleanup:")
            );
            assert!(!dump.contains("If {") && !dump.contains("Loop {") && !dump.contains("Scope("));
        }
        if stage == "cpp" {
            assert!(dump.contains("goto rusk_block_") && !dump.contains("while (true)"));
        }
    }
    let out = case.run("");
    assert!(out.status.success());
    assert_eq!(out.stdout, b"aa\n6\n8\n");
}

#[test]
fn jump_edges_release_borrows_and_return_values_keep_their_owners() {
    let source = include_str!("../examples/beta05/control_flow.rusk");
    let case = Case::new(source);
    let out = case.run("");
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, b"b c\nab!\nab!? 2\n13\n");
    let plain = case.run_with_options("", &["--no-opt"]);
    assert_eq!(out.stdout, plain.stdout);
    assert_eq!(out.stderr, plain.stderr);
    assert_eq!(out.status.code(), plain.status.code());
}

#[test]
fn semantic_failures_are_rejected_before_hir_and_lir_output() {
    for stage in ["hir", "lir", "cpp"] {
        let case = Case::new("fn f(x:Int)->Int{return x;}wt f(true);");
        let out = case.compile_with_options(&["--emit", stage]);
        assert!(!out.status.success());
        assert!(!case.0.join("main.cpp").exists());
    }
    let opaque = Case::new(r#"extern type Iter<Int>{cpp_name:"std::int64_t",} wt 7;"#);
    let out = opaque.run("");
    assert!(out.status.success());
    assert_eq!(out.stdout, b"7\n");
    let case = Case::new("let x:Int;wt x;");
    assert!(
        case.compile_with_options(&["--emit", "ast"])
            .status
            .success()
    );
    assert!(
        !case
            .compile_with_options(&["--emit", "hir"])
            .status
            .success()
    );
}

#[test]
fn inferred_effects_and_return_aliases_are_preserved_in_both_irs() {
    let case = Case::new(
        r#"
struct Item { value: Int; }
fn identity(x: Int) -> Int { return x; }
fn element(item: Item) -> Int { return item.value; }
fn wrapped(x: Int) -> Item { return Item { value: x }; }
fn fresh(x: Int) -> Int { return 7; }
fn rebound(x: Int) -> Int { x := 7; return x; }
extern fn opaque(x: Int) -> Int {
    cpp_name: "test_opaque",
    code: "Obj<std::int64_t> test_opaque(Obj<std::int64_t> x,Loc){return x;}",
}
fn external(x: Int) -> Int { return opaque(x); }
fn apply<F>(f: F, x: Int) -> Int { return f(x); }
let captured := 5;
let callback := (x: Int) => captured;
wt apply(callback, 99);
wt identity(3), element(wrapped(4)), fresh(0), rebound(0), external(5);
"#,
    );
    fn summary<'a>(dump: &'a str, name: &str) -> &'a str {
        let name = format!("name: \"{name}\",");
        let function = &dump[dump.find(&name).unwrap()..];
        let effects = &function[function.find("effects: Summary {").unwrap()..];
        &effects[..effects.find("\n            },").unwrap()]
    }
    for stage in ["hir", "lir"] {
        let out = case.compile_with_options(&["--emit", stage]);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let dump = std::fs::read_to_string(case.0.join("main.cpp")).unwrap();
        let identity = summary(&dump, "identity");
        assert!(identity.contains("source: Inferred") && identity.contains("parameter: 0"));
        assert!(identity.contains("write: No") && identity.contains("escape: May"));
        let element = summary(&dump, "element");
        assert!(element.contains("read: May") && element.contains("Field("));
        assert!(summary(&dump, "wrapped").contains("Field("));
        let applied = summary(&dump, "apply");
        assert!(applied.contains("Field(") && applied.contains("parameter: 0"));
        assert!(applied.contains("write: No"));
        for name in ["fresh", "rebound"] {
            let effects = summary(&dump, name);
            assert!(effects.contains("aliases: {}") && effects.contains("fresh: true"));
            assert!(effects.contains("write: No") && effects.contains("escape: No"));
        }
        let opaque = summary(&dump, "opaque");
        assert!(opaque.contains("source: Opaque") && opaque.contains("write: Unknown"));
        assert!(summary(&dump, "external").contains("write: Unknown"));
    }
}

#[test]
fn cpp_omits_definitions_reached_only_from_unused_code() {
    let case = Case::new(
        r#"
extern fn hidden(x:Int)->Int {
    cpp_name:"test_hidden_native",
    code:"Obj<std::int64_t> test_hidden_native(Obj<std::int64_t> x,Loc){return x;}",
}
enum HiddenEnum { Value(Int) }
struct HiddenRecord { item: HiddenEnum; }
fn idle(x:Int)->Int {
    let item:=HiddenRecord{item:HiddenEnum::Value(hidden(x))};
    return match item.item {Value(n)=>n,};
}
fn used(x:Int)->Int {return x+1;}
wt used(41);
"#,
    );
    let invalid = Case::new("fn idle()->Int{return \"wrong\";} wt 42;");
    for options in [&[][..], &["--no-opt"][..]] {
        let output = case.run_with_options("", options);
        assert!(output.status.success());
        assert_eq!(output.stdout, b"42\n");
        let cpp = std::fs::read_to_string(case.0.join("main.cpp")).unwrap();
        let (body, _) = cpp.split_once("\n// Rusk source: ").unwrap();
        assert!(!body.contains(": idle\n"));
        assert!(!body.contains("test_hidden_native"));
        for prefix in ["struct RuskRecord", "struct RuskEnum"] {
            assert!(
                !body
                    .lines()
                    .any(|line| line.strip_prefix(prefix).is_some_and(|suffix| suffix
                        .as_bytes()
                        .first()
                        .is_some_and(u8::is_ascii_digit)))
            );
        }
        assert!(body.contains(": used\n"));

        let output = invalid.compile_with_options(options);
        assert!(!output.status.success());
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("type mismatch: expected Int, found Str")
        );
    }
}

#[test]
fn standard_runtime_groups_follow_reachable_declarations() {
    let idle = Case::new(r#"fn idle()->Vec<Int>{return suffix_array("abc");}"#);
    let used = Case::new(r#"wt suffix_array("banana")[0];"#);
    let legacy = Case::new(
        r#"
extern symbol zz_legacy {
    code:"const auto audit_initialized = []{ std::cout << sizeof(RuskBigInt) / sizeof(RuskBigInt) << '\\n'; return true; }();",
}
wt 2;
"#,
    );
    for options in [&[][..], &["--no-opt"][..]] {
        assert!(idle.compile_with_options(options).status.success());
        let cpp = std::fs::read_to_string(idle.0.join("main.cpp")).unwrap();
        let (body, _) = cpp.split_once("\n// Rusk source: ").unwrap();
        assert!(!body.contains("using RuskSuffixIndices"));
        assert!(!body.contains("struct RuskBigInt"));

        let output = used.run_with_options("", options);
        assert!(output.status.success());
        assert_eq!(output.stdout, b"5\n");
        let cpp = std::fs::read_to_string(used.0.join("main.cpp")).unwrap();
        let (body, _) = cpp.split_once("\n// Rusk source: ").unwrap();
        assert!(body.contains("using RuskSuffixIndices"));
        assert!(!body.contains("struct RuskBigInt"));

        let output = legacy.run_with_options("", options);
        assert!(output.status.success());
        assert_eq!(output.stdout, b"1\n2\n");
    }
}

#[test]
fn legacy_native_cpp_can_call_an_extern_by_its_cpp_name() {
    let case = Case::new(
        r#"
extern fn entry(x:Int)->Int {
    cpp_name:"audit_entry",
    code:"Obj<std::int64_t> audit_helper(Obj<std::int64_t>,Loc); Obj<std::int64_t> audit_entry(Obj<std::int64_t> x,Loc loc){return audit_helper(x,loc);}",
}
extern fn helper(x:Int)->Int {
    cpp_name:"audit_helper",
    code:"Obj<std::int64_t> audit_helper(Obj<std::int64_t> x,Loc){return x;}",
}
fn idle(x:Int)->Int {return helper(x);}
wt entry(42);
"#,
    );
    for options in [&[][..], &["--no-opt"][..]] {
        let output = case.run_with_options("", options);
        assert!(output.status.success());
        assert_eq!(output.stdout, b"42\n");
    }
}

#[test]
fn concrete_native_templates_emit_only_transitively_reachable_functions() {
    let case = Case::new(
        r#"
struct Seed<T> { value:T; }
extern fn entry(x:Seed<Int>)->Int {
    template:"true",
    cpp_name:"tracked_entry",
    code:"@{return Int} @{fn}(Obj<@{Seed<Int>}> x,Loc loc){return make_obj<@{Int}>(@{value_call helper(Seed<Int>)->Int}(x,loc));}",
}
extern fn helper(x:Seed<Int>)->Int {
    template:"true",
    cpp_name:"tracked_helper",
    code:"@{return Int} @{fn}(Obj<@{Seed<Int>}> x,Loc loc){return @{call leaf(Seed<Int>)->Int}(x,loc);}",
}
fn leaf(x:Seed<Int>)->Int {return x.value+1;}
extern fn helper(x:Str)->Str {
    template:"true",
    cpp_name:"tracked_unused_overload",
    code:"@{return Str} @{fn}(Obj<@{Str}> x,Loc){return x;}",
}
extern fn hidden(x:Int)->Int {
    template:"true",
    cpp_name:"tracked_hidden",
    code:"@{return Int} @{fn}(Obj<@{Int}> x,Loc loc){return @{call dead_leaf(Int)->Int}(x,loc);}",
}
fn dead_leaf(x:Int)->Int {return x-1;}
fn idle(x:Int)->Int {return hidden(x);}
wt entry(Seed::<Int>{value:41});
"#,
    );
    for options in [&[][..], &["--no-opt"][..]] {
        let output = case.run_with_options("", options);
        assert!(output.status.success());
        assert_eq!(output.stdout, b"42\n");
        let cpp = std::fs::read_to_string(case.0.join("main.cpp")).unwrap();
        let (body, _) = cpp.split_once("\n// Rusk source: ").unwrap();
        for included in ["tracked_entry(", "tracked_helper(", ": leaf\n"] {
            assert!(body.contains(included), "{included}");
        }
        for excluded in [
            "tracked_hidden(",
            "tracked_unused_overload(",
            ": idle\n",
            ": dead_leaf\n",
        ] {
            assert!(!body.contains(excluded), "{excluded}");
        }
    }
}

#[test]
fn unused_concrete_native_templates_still_validate_typed_references() {
    let case = Case::new(
        r#"
extern fn idle(x:Int)->Int {
    template:"true",
    cpp_name:"tracked_invalid",
    code:"@{return Int} @{fn}(Obj<@{Int}> x,Loc loc){return @{call missing(Int)->Int}(x,loc);}",
}
wt 1;
"#,
    );
    let output = case.compile();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("no matching native callable 'missing'")
    );
}
