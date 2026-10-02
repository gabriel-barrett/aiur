//! Run a Lean-produced IxVM execution package without transporting the full
//! query record back through JSON. Execution uses the same VM as the Lean FFI.
use aiur::{Program, bytecode::CheckedProgram, execute::Execution, hints::HintEntry};
use serde::Deserialize;
use std::{error::Error, time::Instant};

#[derive(Deserialize)]
struct Package {
    program: Program,
    address: Vec<u64>,
    hints: Vec<HintEntry>,
    #[serde(default)]
    invalid_address: Vec<u64>,
}

fn run(
    program: &CheckedProgram,
    name: &str,
    args: Vec<u64>,
    hints: &[HintEntry],
) -> Result<Execution, Box<dyn Error>> {
    let start = Instant::now();
    let result = program.execute_with_hints(name, args, hints)?;
    let elapsed = start.elapsed();
    if !result.output.is_empty() {
        return Err(format!("{name} returned a non-unit result").into());
    }
    let saved: usize = result.queries.values().map(|q| q.hints.len()).sum();
    let uses: u64 = result.queries.values().map(|q| q.multiplicity).sum();
    println!(
        "{name}: OK ({:.3}s, {} instructions, {} queries, {} query uses, {} ROM cells, {} saved hints)",
        elapsed.as_secs_f64(),
        result.instructions,
        result.queries.len(),
        uses,
        result.memory.len(),
        saved,
    );
    Ok(result)
}

fn benchmark(
    program: &CheckedProgram,
    package: &Package,
    samples: usize,
) -> Result<(), Box<dyn Error>> {
    if samples == 0 {
        return Err("benchmark requires at least one sample".into());
    }
    let start = Instant::now();
    let hints = program.prepare_hints(&package.hints)?;
    let preparation_seconds = start.elapsed().as_secs_f64();
    let mut times = Vec::with_capacity(samples);
    let mut counts = None;
    for i in 0..samples + 3 {
        let args = package.address.clone();
        let start = Instant::now();
        let result = hints.execute("IxVM::verify_transitive", args)?;
        let seconds = start.elapsed().as_secs_f64();
        assert!(result.output.is_empty());
        let observed = (
            result.instructions,
            result.queries.len(),
            result
                .queries
                .keys()
                .filter(|q| q.function < program.program().functions.len())
                .count(),
            result.queries.values().map(|q| q.multiplicity).sum::<u64>(),
            result.memory.len(),
            result
                .queries
                .values()
                .map(|q| q.hints.len())
                .sum::<usize>(),
        );
        if let Some(expected) = counts {
            assert_eq!(observed, expected, "fresh runs must do the same work");
        }
        counts = Some(observed);
        if i >= 3 {
            times.push(seconds);
        }
        // Drop the returned query record outside the measured interval.
    }
    let (instructions, queries, function_queries, uses, memory, saved) = counts.unwrap();
    println!(
        "{}",
        serde_json::json!({
            "engine": "new-aiur-bytecode", "warmups": 3,
            "seconds": times, "hint_preparation_seconds": preparation_seconds,
            "instructions": instructions, "queries": queries, "query_uses": uses,
            "function_queries": function_queries, "map_queries": queries - function_queries,
            "rom_cells": memory, "saved_hints": saved,
        })
    );
    Ok(())
}

fn rejected(
    program: &CheckedProgram,
    label: &str,
    args: Vec<u64>,
    hints: &[HintEntry],
    reason: &str,
) -> Result<(), Box<dyn Error>> {
    match program.execute_with_hints("IxVM::verify_constant", args, hints) {
        Ok(_) => Err(format!("accepted {label}").into()),
        Err(e) if e.message.contains(reason) => {
            println!("{label}: rejected ({e})");
            Ok(())
        }
        Err(e) => Err(format!("{label}: wrong rejection: {e}; expected {reason}").into()),
    }
}

fn negatives(program: &CheckedProgram, package: &Package) -> Result<(), Box<dyn Error>> {
    let mut key = vec![2];
    key.extend(&package.address);
    let info = package
        .hints
        .iter()
        .position(|h| h.key == key && h.output.len() == 2)
        .ok_or("fixture has no target stream")?;
    let offset = package.hints[info].output[0];
    let byte = package
        .hints
        .iter()
        .position(|h| h.key == [2, offset] && h.output.len() == 1)
        .ok_or("fixture has no target byte")?;
    let mut bad = package.hints.clone();
    bad[byte].output[0] ^= 1;
    rejected(
        program,
        "corrupted serialization",
        package.address.clone(),
        &bad,
        "blake3",
    )?;

    let mut bad = package.hints.clone();
    let mut digest = package.address.clone();
    digest[0] ^= 1;
    bad[info].key[1..].copy_from_slice(&digest);
    rejected(program, "wrong Blake3 address", digest, &bad, "blake3")?;

    let mut bad = package.hints.clone();
    bad.remove(byte);
    rejected(
        program,
        "missing byte hint",
        package.address.clone(),
        &bad,
        "missing hint",
    )?;
    if !package.invalid_address.is_empty() {
        rejected(
            program,
            "correctly hashed invalid proof",
            package.invalid_address.clone(),
            &package.hints,
            "inferred type is not def-eq",
        )?;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    let path = args.get(1).ok_or(
        "usage: ixvm_stage1 PACKAGE.json [all|primitives|serde|constant|transitive|negative|bench [SAMPLES]]",
    )?;
    let mode = args.get(2).map(String::as_str).unwrap_or("all");
    let package: Package = serde_json::from_slice(&std::fs::read(path)?)?;
    let program = package.program.clone().check()?;
    if mode == "bench" {
        return benchmark(
            &program,
            &package,
            args.get(3).map(|s| s.parse()).transpose()?.unwrap_or(20),
        );
    }
    let entries = [
        ("primitives", "IxVM::check_primitives"),
        ("serde", "IxVM::verify_serde"),
        ("constant", "IxVM::verify_constant"),
        ("transitive", "IxVM::verify_transitive"),
    ];
    if mode != "all" && mode != "negative" && !entries.iter().any(|(m, _)| *m == mode) {
        return Err(format!("unknown mode: {mode}").into());
    }
    for (selected, entry) in entries {
        if mode == "all" || mode == selected {
            run(
                &program,
                entry,
                if selected == "primitives" {
                    vec![]
                } else {
                    package.address.clone()
                },
                &package.hints,
            )?;
        }
    }
    if mode == "all" || mode == "negative" {
        negatives(&program, &package)?;
    }
    Ok(())
}
