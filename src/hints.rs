//! Per-execution witness data. Keys include both concrete types: equal-width
//! encodings of different nominal types or tuple shapes are not interchangeable.
use crate::bytecode::{CheckedProgram, Type};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HintEntry {
    pub r#type: Type,
    pub key_type: Type,
    pub key: Vec<u64>,
    pub output: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct HintKey {
    pub r#type: Type,
    pub key_type: Type,
    pub key: Vec<u64>,
}

/// Immutable, validated witness data tied to the program that defines its
/// layouts and field. Reusing it never reuses execution caches or ROM pointers.
pub struct PreparedHints<'a> {
    pub(crate) program: &'a CheckedProgram,
    pub(crate) index: HashMap<HintKey, Vec<u64>>,
}

impl CheckedProgram {
    pub fn prepare_hints(&self, entries: &[HintEntry]) -> Result<PreparedHints<'_>, String> {
        Ok(PreparedHints {
            program: self,
            index: prepare(self, entries)?,
        })
    }
}

/// An answer actually consumed by this query's first successful execution.
/// The query's function ID and this instruction identify its bytecode site.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct HintAnswer {
    pub instruction: usize,
    pub r#type: Type,
    pub key_type: Type,
    pub key: Vec<u64>,
    pub output: Vec<u64>,
}

pub(crate) fn prepare(
    program: &CheckedProgram,
    entries: &[HintEntry],
) -> Result<HashMap<HintKey, Vec<u64>>, String> {
    let mut layouts = HashMap::new();
    let mut index = HashMap::new();
    for (row, entry) in entries.iter().enumerate() {
        let check = |ty: &Type, words: &[u64], layouts: &mut HashMap<_, _>| {
            if !layouts.contains_key(ty) {
                let layout = ty.layout(&program.program.enums, &mut vec![])?;
                if !layout.pointer_free() {
                    return Err("supplied hint data cannot contain pointers".to_owned());
                }
                layouts.insert(ty.clone(), layout);
            }
            layouts[ty].validate(words, program.field)
        };
        check(&entry.key_type, &entry.key, &mut layouts)
            .map_err(|e| format!("hint entry {row} key: {e}"))?;
        check(&entry.r#type, &entry.output, &mut layouts)
            .map_err(|e| format!("hint entry {row} output: {e}"))?;
        let key = HintKey {
            r#type: entry.r#type.clone(),
            key_type: entry.key_type.clone(),
            key: entry.key.clone(),
        };
        match index.entry(key) {
            std::collections::hash_map::Entry::Vacant(slot) => {
                slot.insert(entry.output.clone());
            }
            std::collections::hash_map::Entry::Occupied(slot) => {
                if *slot.get() != entry.output {
                    return Err(format!("conflicting hint entries at row {row}"));
                }
            }
        }
    }
    Ok(index)
}
