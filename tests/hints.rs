use aiur::bytecode::{
    Constructor, Entry, Enum, Function, Instruction as Op, Program, Type, VERSION,
};
use aiur::execute::QueryInput;
use aiur::hints::HintEntry;
use aiur::value::IoType;

fn function(name: &str, registers: usize, code: Vec<Op>) -> Function {
    Function {
        name: name.into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers,
        code,
    }
}

fn program(functions: Vec<Function>, entry: usize) -> Program {
    Program {
        version: VERSION,
        modulus: 97,
        functions,
        enums: vec![],
        tables: vec![],
        maps: vec![],
        entries: vec![Entry {
            name: "main".into(),
            function: entry,
            inputs: vec![IoType::Field],
            output: None,
        }],
    }
}

fn hint(key: usize, dest: usize) -> Op {
    Op::Hint {
        r#type: Type::Field,
        key_type: Type::Field,
        key: vec![key],
        dest: vec![dest],
    }
}

fn row(key: u64, output: u64) -> HintEntry {
    HintEntry {
        r#type: Type::Field,
        key_type: Type::Field,
        key: vec![key],
        output: vec![output],
    }
}

#[test]
fn dynamic_keys_and_consumed_answers_belong_to_cached_queries() {
    let child = function(
        "child",
        2,
        vec![hint(0, 1), hint(1, 1), Op::Ret { value: vec![1] }],
    );
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
            hint(1, 1),
            Op::Ret { value: vec![1] },
        ],
    );
    let p = program(vec![child, parent], 1).check().unwrap();
    let entries = [row(4, 5), row(5, 6), row(6, 7)];
    let result = p.execute_with_hints("main", vec![4], &entries).unwrap();
    assert_eq!(result.output, vec![7]);
    let child = &result.queries[&QueryInput {
        function: 0,
        args: vec![4],
    }];
    assert_eq!(child.multiplicity, 2);
    assert_eq!(child.hints.len(), 2);
    assert_eq!(child.hints[0].instruction, 0);
    assert_eq!(child.hints[0].key, vec![4]);
    assert_eq!(child.hints[0].output, vec![5]);
    assert_eq!(child.hints[1].instruction, 1);
    assert_eq!(child.hints[1].key, vec![5]);
    assert_eq!(child.hints[1].output, vec![6]);
    let parent = &result.queries[&QueryInput {
        function: 1,
        args: vec![4],
    }];
    assert_eq!(parent.hints.len(), 1);
    assert_eq!(parent.hints[0].output, vec![7]);
    // A fresh session can select different witnesses for the same root query.
    let again = p
        .execute_with_hints("main", vec![4], &[row(4, 5), row(5, 6), row(6, 8)])
        .unwrap();
    assert_eq!(again.output, vec![8]);
    assert!(
        p.execute("main", vec![4])
            .unwrap_err()
            .message
            .contains("missing hint")
    );
}

#[test]
fn types_disambiguate_identical_word_encodings() {
    let nominal = |name: &str| Type::Enum { name: name.into() };
    let single = Type::Tuple {
        items: vec![Type::Field],
    };
    let signatures = [
        (Type::Field, Type::Field),
        (Type::Field, single),
        (Type::Field, nominal("A")),
        (Type::Field, nominal("B")),
        (nominal("A"), Type::Field),
        (nominal("B"), Type::Field),
    ];
    let mut instructions = signatures
        .iter()
        .enumerate()
        .map(|(i, (result, key))| Op::Hint {
            r#type: result.clone(),
            key_type: key.clone(),
            key: vec![0],
            dest: vec![i + 1],
        })
        .collect::<Vec<_>>();
    instructions.push(Op::Ret {
        value: (1..=6).collect(),
    });
    let mut f = function("typed", 7, instructions);
    f.result = Type::Tuple {
        items: signatures
            .iter()
            .map(|(result, _)| result.clone())
            .collect(),
    };
    let mut p = program(vec![f], 0);
    p.enums = ["A", "B"]
        .map(|name| Enum {
            name: name.into(),
            constructors: vec![Constructor {
                name: "Wrap".into(),
                fields: vec![Type::Field],
            }],
        })
        .to_vec();
    let entries = signatures
        .iter()
        .enumerate()
        .map(|(i, (result, key))| HintEntry {
            r#type: result.clone(),
            key_type: key.clone(),
            key: vec![7],
            output: vec![i as u64 + 10],
        })
        .collect::<Vec<_>>();
    let result = p
        .check()
        .unwrap()
        .execute_with_hints("main", vec![7], &entries)
        .unwrap();
    assert_eq!(result.output, vec![10, 11, 12, 13, 14, 15]);
}

#[test]
fn repeated_identical_data_is_allowed_but_conflicts_are_errors() {
    let p = program(
        vec![function(
            "hinted",
            2,
            vec![hint(0, 1), Op::Ret { value: vec![1] }],
        )],
        0,
    )
    .check()
    .unwrap();
    let result = p
        .execute_with_hints("main", vec![4], &[row(4, 5), row(4, 5)])
        .unwrap();
    assert_eq!(result.output, vec![5]);
    assert!(
        p.execute_with_hints("main", vec![4], &[row(4, 5), row(4, 6)])
            .unwrap_err()
            .message
            .contains("conflicting hint entries")
    );
    // Conflict checking also covers data the execution would never request.
    assert!(
        p.execute_with_hints("main", vec![4], &[row(4, 5), row(9, 1), row(9, 2)])
            .unwrap_err()
            .message
            .contains("conflicting hint entries")
    );
}

#[test]
fn inactive_sites_do_not_request_or_record_answers() {
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
                hint(0, 1),
                Op::Ret { value: vec![1] },
            ],
        )],
        0,
    )
    .check()
    .unwrap();
    let result = p.execute("main", vec![0]).unwrap();
    assert!(result.queries.values().all(|q| q.hints.is_empty()));
    let error = p.execute("main", vec![1]).unwrap_err();
    assert_eq!(error.instruction, 2);
    assert_eq!(error.function, "lazy");
}

#[test]
fn flat_data_validates_nested_tags_padding_fields_widths_and_pointers() {
    let nominal = |name: &str| Type::Enum { name: name.into() };
    let mut p = program(
        vec![function("identity", 1, vec![Op::Ret { value: vec![0] }])],
        0,
    );
    p.enums = vec![
        Enum {
            name: "Inner".into(),
            constructors: vec![
                Constructor {
                    name: "None".into(),
                    fields: vec![],
                },
                Constructor {
                    name: "Some".into(),
                    fields: vec![Type::Field],
                },
            ],
        },
        Enum {
            name: "Outer".into(),
            constructors: vec![
                Constructor {
                    name: "Empty".into(),
                    fields: vec![],
                },
                Constructor {
                    name: "Wrap".into(),
                    fields: vec![nominal("Inner")],
                },
            ],
        },
        Enum {
            name: "HiddenPointer".into(),
            constructors: vec![
                Constructor {
                    name: "Empty".into(),
                    fields: vec![],
                },
                Constructor {
                    name: "Ptr".into(),
                    fields: vec![Type::Ptr {
                        target: Box::new(Type::Field),
                    }],
                },
            ],
        },
    ];
    let p = p.check().unwrap();
    let good = HintEntry {
        r#type: nominal("Outer"),
        key_type: nominal("Outer"),
        key: vec![1, 1, 7],
        output: vec![1, 0, 0],
    };
    p.execute_with_hints("main", vec![0], std::slice::from_ref(&good))
        .unwrap();
    for (words, expected) in [
        (vec![1, 2, 0], "invalid enum tag"),
        (vec![1, 0, 1], "nonzero enum padding"),
        (vec![0, 1, 0], "nonzero enum padding"),
        (vec![1, 1, 97], "noncanonical"),
        (vec![1, 1], "width"),
    ] {
        for key in [false, true] {
            let mut bad = good.clone();
            if key {
                bad.key = words.clone();
            } else {
                bad.output = words.clone();
            }
            let error = p.execute_with_hints("main", vec![0], &[bad]).unwrap_err();
            assert!(error.message.contains(expected), "{}", error.message);
        }
    }
    let pointer = HintEntry {
        r#type: nominal("HiddenPointer"),
        key_type: Type::Field,
        key: vec![0],
        output: vec![0, 0],
    };
    assert!(
        p.execute_with_hints("main", vec![0], &[pointer])
            .unwrap_err()
            .message
            .contains("pointers")
    );
    let unknown = HintEntry {
        r#type: nominal("Unknown"),
        ..row(0, 1)
    };
    assert!(
        p.execute_with_hints("main", vec![0], &[unknown])
            .unwrap_err()
            .message
            .contains("unknown enum")
    );
}

#[test]
fn zero_width_answers_still_have_distinct_nominal_keys() {
    let unit = Type::Enum {
        name: "Unit".into(),
    };
    let mut f = function(
        "unit",
        1,
        vec![
            Op::Hint {
                r#type: unit.clone(),
                key_type: unit.clone(),
                key: vec![],
                dest: vec![],
            },
            Op::Ret { value: vec![] },
        ],
    );
    f.result = unit.clone();
    let mut p = program(vec![f], 0);
    p.enums.push(Enum {
        name: "Unit".into(),
        constructors: vec![Constructor {
            name: "Unit".into(),
            fields: vec![],
        }],
    });
    let p = p.check().unwrap();
    let wrong_key = HintEntry {
        r#type: unit.clone(),
        key_type: Type::Tuple { items: vec![] },
        key: vec![],
        output: vec![],
    };
    assert!(
        p.execute_with_hints("main", vec![0], &[wrong_key])
            .unwrap_err()
            .message
            .contains("missing hint")
    );
    let entry = HintEntry {
        r#type: unit.clone(),
        key_type: unit,
        key: vec![],
        output: vec![],
    };
    let result = p.execute_with_hints("main", vec![0], &[entry]).unwrap();
    assert!(result.output.is_empty());
    assert_eq!(result.queries.values().next().unwrap().hints.len(), 1);
}
