use aiur::bytecode::{Binary, Entry, Function, Instruction as Op, Program, Type, VERSION};
use aiur::execute::QueryInput;
use aiur::field::PrimeField;
use aiur::value::{IoType, Value};
use serde_json::json;

fn function(name: &str, registers: usize, code: Vec<Op>) -> Function {
    Function {
        name: name.into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers,
        code,
    }
}
fn program(functions: Vec<Function>, root: usize) -> Program {
    Program {
        version: VERSION,
        modulus: 65_537,
        functions,
        enums: vec![],
        tables: vec![],
        maps: vec![],
        entries: vec![Entry {
            name: "main".into(),
            function: root,
            inputs: vec![IoType::Field],
            output: Some(IoType::Field),
        }],
    }
}
fn fib() -> Function {
    function(
        "fib",
        7,
        vec![
            Op::Branch {
                tests: vec![(0, 0)],
                otherwise: 3,
            },
            Op::Literal { dest: 1, value: 0 },
            Op::Ret { value: vec![1] },
            Op::Branch {
                tests: vec![(0, 1)],
                otherwise: 6,
            },
            Op::Literal { dest: 1, value: 1 },
            Op::Ret { value: vec![1] },
            Op::Literal { dest: 1, value: 1 },
            Op::Binary {
                dest: 2,
                operator: Binary::Sub,
                left: 0,
                right: 1,
            },
            Op::Call {
                function: 0,
                args: vec![2],
                dest: vec![3],
            },
            Op::Binary {
                dest: 4,
                operator: Binary::Sub,
                left: 2,
                right: 1,
            },
            Op::Call {
                function: 0,
                args: vec![4],
                dest: vec![5],
            },
            Op::Binary {
                dest: 6,
                operator: Binary::Add,
                left: 3,
                right: 5,
            },
            Op::Ret { value: vec![6] },
        ],
    )
}

#[test]
fn memoized_fibonacci_and_isolated_sessions() {
    let p = program(vec![fib()], 0).check().unwrap();
    let result = p.execute("main", vec![20]).unwrap();
    assert_eq!(result.output, vec![6765]);
    assert_eq!(result.queries.len(), 21);
    assert!(result.instructions < 250);
    assert_eq!(
        result.queries[&QueryInput {
            function: 0,
            args: vec![18]
        }]
            .multiplicity,
        2
    );
    let again = p.execute("main", vec![20]).unwrap();
    assert_eq!(result.queries, again.queries);
}

#[test]
fn hits_do_not_reexecute_callees_and_counts_do_not_wrap_in_the_field() {
    let leaf = function("leaf", 1, vec![Op::Ret { value: vec![0] }]);
    let parent = function(
        "parent",
        2,
        vec![
            Op::Call {
                function: 0,
                args: vec![0],
                dest: vec![1],
            },
            Op::Call {
                function: 0,
                args: vec![0],
                dest: vec![1],
            },
            Op::Ret { value: vec![1] },
        ],
    );
    let mut calls = vec![
        Op::Call {
            function: 1,
            args: vec![0],
            dest: vec![1]
        };
        5
    ];
    calls.push(Op::Ret { value: vec![1] });
    let root = function("root", 2, calls);
    let mut p = program(vec![leaf, parent, root], 2);
    p.modulus = 2;
    let result = p.check().unwrap().execute("main", vec![1]).unwrap();
    assert_eq!(
        result.queries[&QueryInput {
            function: 2,
            args: vec![1]
        }]
            .multiplicity,
        1
    );
    assert_eq!(
        result.queries[&QueryInput {
            function: 1,
            args: vec![1]
        }]
            .multiplicity,
        5
    );
    assert_eq!(
        result.queries[&QueryInput {
            function: 0,
            args: vec![1]
        }]
            .multiplicity,
        2
    );
}

#[test]
fn mutual_recursion_uses_a_vm_stack() {
    fn countdown(name: &str, next: usize) -> Function {
        function(
            name,
            3,
            vec![
                Op::Branch {
                    tests: vec![(0, 0)],
                    otherwise: 2,
                },
                Op::Ret { value: vec![0] },
                Op::Literal { dest: 1, value: 1 },
                Op::Binary {
                    dest: 2,
                    operator: Binary::Sub,
                    left: 0,
                    right: 1,
                },
                Op::Call {
                    function: next,
                    args: vec![2],
                    dest: vec![1],
                },
                Op::Ret { value: vec![1] },
            ],
        )
    }
    let p = program(vec![countdown("a", 1), countdown("b", 0)], 0)
        .check()
        .unwrap();
    let result = p.execute("main", vec![20_000]).unwrap();
    assert_eq!(result.output, vec![0]);
    assert_eq!(result.queries.len(), 20_001);
}

#[test]
fn pending_cycle_is_an_error() {
    let p = program(
        vec![function(
            "cycle",
            1,
            vec![
                Op::Call {
                    function: 0,
                    args: vec![0],
                    dest: vec![0],
                },
                Op::Ret { value: vec![0] },
            ],
        )],
        0,
    )
    .check()
    .unwrap();
    assert!(
        p.execute("main", vec![1])
            .unwrap_err()
            .message
            .contains("already being evaluated")
    );
    assert!(
        p.execute("hidden", vec![1])
            .unwrap_err()
            .message
            .contains("unselected")
    );
}

#[test]
fn invalid_control_flow_and_uninitialized_reads_are_rejected() {
    for code in [
        vec![Op::Jump { target: 0 }],
        vec![Op::Ret { value: vec![1] }],
        vec![
            Op::Literal { dest: 2, value: 3 },
            Op::Ret { value: vec![0] },
        ],
        vec![
            Op::Branch {
                tests: vec![(0, 0)],
                otherwise: 2,
            },
            Op::Literal { dest: 1, value: 0 },
            Op::Ret { value: vec![1] },
        ],
    ] {
        assert!(program(vec![function("bad", 2, code)], 0).check().is_err());
    }
}

#[test]
fn inactive_failures_are_not_evaluated() {
    let p = program(
        vec![function(
            "lazy",
            2,
            vec![
                Op::Branch {
                    tests: vec![(0, 0)],
                    otherwise: 2,
                },
                Op::Ret { value: vec![0] },
                Op::Literal { dest: 1, value: 0 },
                Op::Binary {
                    dest: 1,
                    operator: Binary::Div,
                    left: 0,
                    right: 1,
                },
                Op::Ret { value: vec![1] },
            ],
        )],
        0,
    )
    .check()
    .unwrap();
    assert_eq!(p.execute("main", vec![0]).unwrap().output, vec![0]);
    assert!(
        p.execute("main", vec![1])
            .unwrap_err()
            .message
            .contains("division by zero")
    );
}

#[test]
#[should_panic(expected = "keyed nondeterminism provider")]
fn nondeterminism_is_explicitly_todo() {
    let p = program(
        vec![function(
            "hint",
            2,
            vec![
                Op::Hint {
                    r#type: Type::Field,
                    key_type: Type::Field,
                    key: vec![0],
                    dest: vec![1],
                },
                Op::Ret { value: vec![1] },
            ],
        )],
        0,
    )
    .check()
    .unwrap();
    let _ = p.execute("main", vec![1]);
}

#[test]
fn typed_rom_interning_and_capacity() {
    let code = vec![
        Op::Store {
            r#type: Type::Field,
            value: vec![0],
            dest: 1,
        },
        Op::Store {
            r#type: Type::Field,
            value: vec![0],
            dest: 2,
        },
        Op::Load {
            r#type: Type::Field,
            pointer: 1,
            dest: vec![2],
        },
        Op::Ret { value: vec![2] },
    ];
    let p = program(vec![function("rom", 3, code)], 0).check().unwrap();
    let result = p.execute("main", vec![9]).unwrap();
    assert_eq!(result.output, vec![9]);
    assert_eq!(result.memory.len(), 1);
    assert_eq!(result.memory[0].multiplicity, 3);
    let code = vec![
        Op::Store {
            r#type: Type::Field,
            value: vec![0],
            dest: 1,
        },
        Op::Literal { dest: 2, value: 1 },
        Op::Store {
            r#type: Type::Field,
            value: vec![2],
            dest: 1,
        },
        Op::Store {
            r#type: Type::Tuple { items: vec![] },
            value: vec![],
            dest: 1,
        },
        Op::Ret { value: vec![0] },
    ];
    let mut p = program(vec![function("full", 3, code)], 0);
    p.modulus = 2;
    assert!(
        p.check()
            .unwrap()
            .execute("main", vec![0])
            .unwrap_err()
            .message
            .contains("capacity")
    );
}

#[test]
fn structured_io_roundtrips_and_validates_all_enum_padding() {
    let f = PrimeField::new(97).unwrap();
    let unit = IoType::Enum {
        name: "Unit".into(),
        constructors: vec![("Unit".into(), vec![])],
    };
    let ty = IoType::Struct {
        name: "Packet".into(),
        fields: vec![
            (
                "units".into(),
                IoType::Array {
                    element: Box::new(unit),
                    length: 3,
                },
            ),
            (
                "values".into(),
                IoType::Enum {
                    name: "Choice".into(),
                    constructors: vec![
                        ("None".into(), vec![]),
                        (
                            "Some".into(),
                            vec![IoType::Array {
                                element: Box::new(IoType::Field),
                                length: 2,
                            }],
                        ),
                    ],
                },
            ),
            (
                "singleton".into(),
                IoType::Tuple {
                    items: vec![IoType::Field],
                },
            ),
        ],
    };
    let value = ty.read_json(&json!({"singleton":[4],"values":{"Some":[[7,8]]},"units":[{"Unit":[]},{"Unit":[]},{"Unit":[]}]})).unwrap();
    let flat = ty.flatten(&value, f).unwrap();
    assert_eq!(flat, vec![1, 7, 8, 4]);
    assert_eq!(ty.unflatten(&flat, f).unwrap(), value);
    assert_eq!(
        value.to_string(),
        "Packet { units: [Unit::Unit, Unit::Unit, Unit::Unit], values: Choice::Some([7, 8]), singleton: (4,) }"
    );
    assert!(ty.unflatten(&[2, 0, 0, 4], f).is_err());
    assert!(ty.unflatten(&[0, 1, 0, 4], f).is_err());
    assert!(IoType::Field.flatten(&Value::from(97), f).is_err());
    assert!(
        IoType::Tuple { items: vec![] }
            .flatten(&Value::Array { items: vec![] }, f)
            .is_err()
    );
}
