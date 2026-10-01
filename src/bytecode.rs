//! Execution-only interchange format and its one-time validation/linking pass.
use crate::{field::PrimeField, value::IoType};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

pub const VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Type {
    Field,
    Tuple { items: Vec<Type> },
    Ptr { target: Box<Type> },
    Enum { name: String },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Constructor {
    pub name: String,
    pub fields: Vec<Type>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Enum {
    pub name: String,
    pub constructors: Vec<Constructor>,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Binary {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Instruction {
    Literal {
        dest: usize,
        value: u64,
    },
    Copy {
        dest: Vec<usize>,
        source: Vec<usize>,
    },
    Neg {
        dest: usize,
        source: usize,
    },
    Binary {
        dest: usize,
        operator: Binary,
        left: usize,
        right: usize,
    },
    Guard {
        tests: Vec<(usize, u64)>,
        message: String,
    },
    Branch {
        tests: Vec<(usize, u64)>,
        otherwise: usize,
    },
    Jump {
        target: usize,
    },
    Call {
        function: usize,
        args: Vec<usize>,
        dest: Vec<usize>,
    },
    Store {
        r#type: Type,
        value: Vec<usize>,
        dest: usize,
    },
    Load {
        r#type: Type,
        pointer: usize,
        dest: Vec<usize>,
    },
    Hint {
        r#type: Type,
        key_type: Type,
        key: Vec<usize>,
        dest: Vec<usize>,
    },
    AssertEq {
        left: Vec<usize>,
        right: Vec<usize>,
        message: Option<String>,
    },
    Ret {
        value: Vec<usize>,
    },
    Fail {
        message: String,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Function {
    pub name: String,
    pub params: Vec<Type>,
    pub result: Type,
    pub registers: usize,
    pub code: Vec<Instruction>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Table {
    pub name: String,
    pub r#type: Type,
    pub rows: Vec<Vec<u64>>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Map {
    pub name: String,
    pub params: Vec<Type>,
    pub result: Type,
    pub input: usize,
    pub output: usize,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Entry {
    pub name: String,
    pub function: usize,
    /// Only entrypoints retain source IO descriptions.
    pub inputs: Vec<IoType>,
    /// None means the result contains a pointer or opaque type.
    pub output: Option<IoType>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Program {
    pub version: u32,
    pub modulus: u64,
    pub functions: Vec<Function>,
    pub enums: Vec<Enum>,
    pub tables: Vec<Table>,
    pub maps: Vec<Map>,
    pub entries: Vec<Entry>,
}

#[derive(Clone, Debug)]
pub(crate) enum Layout {
    Field,
    Pointer,
    Tuple(Vec<Layout>),
    Enum {
        constructors: Vec<Layout>,
        payload: usize,
    },
}
impl Layout {
    pub(crate) fn width(&self) -> usize {
        match self {
            Self::Field | Self::Pointer => 1,
            Self::Tuple(items) => items.iter().map(Self::width).sum(),
            Self::Enum {
                constructors,
                payload,
            } => payload + usize::from(constructors.len() > 1),
        }
    }
    pub(crate) fn pointer_free(&self) -> bool {
        match self {
            Self::Field => true,
            Self::Pointer => false,
            Self::Tuple(items) => items.iter().all(Self::pointer_free),
            Self::Enum { constructors, .. } => constructors.iter().all(Self::pointer_free),
        }
    }
    pub(crate) fn validate(&self, words: &[u64], field: PrimeField) -> Result<(), String> {
        if words.len() != self.width() || words.iter().any(|v| !field.contains(*v)) {
            return Err("incorrect value width or noncanonical field element".into());
        }
        match self {
            Self::Field | Self::Pointer => Ok(()),
            Self::Tuple(items) => {
                let mut offset = 0;
                for item in items {
                    item.validate(&words[offset..offset + item.width()], field)?;
                    offset += item.width();
                }
                Ok(())
            }
            Self::Enum { constructors, .. } => {
                let (tag, payload) = if constructors.len() > 1 {
                    (
                        usize::try_from(words[0]).map_err(|_| "enum tag too large")?,
                        &words[1..],
                    )
                } else {
                    (0, words)
                };
                let ctor = constructors.get(tag).ok_or("invalid enum tag")?;
                ctor.validate(&payload[..ctor.width()], field)?;
                if payload[ctor.width()..].iter().any(|v| *v != 0) {
                    return Err("nonzero enum padding".into());
                }
                Ok(())
            }
        }
    }
}

impl Type {
    fn layout(&self, enums: &[Enum], path: &mut Vec<String>) -> Result<Layout, String> {
        match self {
            Self::Field => Ok(Layout::Field),
            Self::Ptr { .. } => Ok(Layout::Pointer),
            Self::Tuple { items } => Ok(Layout::Tuple(
                items
                    .iter()
                    .map(|t| t.layout(enums, path))
                    .collect::<Result<_, _>>()?,
            )),
            Self::Enum { name } => {
                if path.contains(name) {
                    return Err(format!("recursive inline layout {name}"));
                }
                let decl = enums
                    .iter()
                    .find(|e| e.name == *name)
                    .ok_or_else(|| format!("unknown enum {name}"))?;
                path.push(name.clone());
                let constructors = decl
                    .constructors
                    .iter()
                    .map(|c| {
                        Type::Tuple {
                            items: c.fields.clone(),
                        }
                        .layout(enums, path)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                path.pop();
                let payload = constructors.iter().map(Layout::width).max().unwrap_or(0);
                Ok(Layout::Enum {
                    constructors,
                    payload,
                })
            }
        }
    }
}

/// Validated bytecode plus prebuilt indexes shared by all maps using a table.
#[derive(Debug)]
pub struct CheckedProgram {
    pub(crate) program: Program,
    pub(crate) field: PrimeField,
    pub(crate) inputs: Vec<Layout>,
    pub(crate) outputs: Vec<Layout>,
    pub(crate) memory_layouts: HashMap<Type, Layout>,
    pub(crate) map_indexes: HashMap<usize, HashMap<Vec<u64>, usize>>,
}
impl CheckedProgram {
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn field(&self) -> PrimeField {
        self.field
    }
    pub fn entry(&self, name: &str) -> Result<&Entry, String> {
        self.program
            .entries
            .iter()
            .find(|e| e.name == name)
            .ok_or_else(|| format!("unselected entrypoint {name}"))
    }
    pub fn callable_name(&self, id: usize) -> Option<&str> {
        if let Some(f) = self.program.functions.get(id) {
            Some(&f.name)
        } else {
            self.program
                .maps
                .get(id.checked_sub(self.program.functions.len())?)
                .map(|m| m.name.as_str())
        }
    }
}

fn unique<'a>(names: impl Iterator<Item = &'a str>) -> Result<(), String> {
    let mut seen = HashSet::new();
    for name in names {
        if !seen.insert(name) {
            return Err(format!("duplicate name {name}"));
        }
    }
    Ok(())
}
impl Program {
    pub fn check(self) -> Result<CheckedProgram, String> {
        if self.version != VERSION {
            return Err(format!(
                "unsupported execution bytecode version {}",
                self.version
            ));
        }
        let field = PrimeField::new(self.modulus)?;
        unique(
            self.functions
                .iter()
                .map(|f| f.name.as_str())
                .chain(self.maps.iter().map(|m| m.name.as_str())),
        )?;
        unique(self.enums.iter().map(|e| e.name.as_str()))?;
        unique(self.tables.iter().map(|t| t.name.as_str()))?;
        unique(self.entries.iter().map(|e| e.name.as_str()))?;
        for decl in &self.enums {
            unique(decl.constructors.iter().map(|c| c.name.as_str()))?;
            if decl.constructors.len() as u128 > u128::from(field.modulus()) {
                return Err("enum tags do not fit in the field".into());
            }
            Type::Enum {
                name: decl.name.clone(),
            }
            .layout(&self.enums, &mut vec![])?;
        }
        let signatures = self
            .functions
            .iter()
            .map(|f| (&f.params, &f.result))
            .chain(self.maps.iter().map(|m| (&m.params, &m.result)));
        let mut inputs = vec![];
        let mut outputs = vec![];
        for (params, result) in signatures {
            inputs.push(
                Type::Tuple {
                    items: params.clone(),
                }
                .layout(&self.enums, &mut vec![])?,
            );
            outputs.push(result.layout(&self.enums, &mut vec![])?);
        }
        for entry in &self.entries {
            let input = inputs
                .get(entry.function)
                .ok_or("invalid entry function ID")?;
            if !input.pointer_free() {
                return Err("entry arguments contain pointers".into());
            }
            let input_width = entry
                .inputs
                .iter()
                .map(IoType::checked_width)
                .collect::<Result<Vec<_>, _>>()?
                .iter()
                .sum::<usize>();
            if input_width != input.width() {
                return Err("entry input description width mismatch".into());
            }
            if let Some(output) = &entry.output
                && (output.checked_width()? != outputs[entry.function].width()
                    || !outputs[entry.function].pointer_free())
            {
                return Err("entry output description mismatch".into());
            }
        }
        for table in &self.tables {
            let layout = table.r#type.layout(&self.enums, &mut vec![])?;
            if !layout.pointer_free() {
                return Err("table contains pointers".into());
            }
            for row in &table.rows {
                layout.validate(row, field)?;
            }
        }
        let mut map_indexes = HashMap::new();
        for map in &self.maps {
            let input = self.tables.get(map.input).ok_or("invalid input table ID")?;
            let output = self
                .tables
                .get(map.output)
                .ok_or("invalid output table ID")?;
            if input.r#type
                != (Type::Tuple {
                    items: map.params.clone(),
                })
                || output.r#type != map.result
                || input.rows.len() != output.rows.len()
            {
                return Err(format!("table/map interface mismatch for {}", map.name));
            }
            if let std::collections::hash_map::Entry::Vacant(entry) = map_indexes.entry(map.input) {
                let mut index = HashMap::new();
                for (i, row) in input.rows.iter().enumerate() {
                    if index.insert(row.clone(), i).is_some() {
                        return Err("duplicate map input row".into());
                    }
                }
                entry.insert(index);
            }
        }
        let mut memory_layouts = HashMap::new();
        for (id, function) in self.functions.iter().enumerate() {
            check_function(
                function,
                inputs[id].width(),
                outputs[id].width(),
                &inputs,
                &outputs,
                &self.enums,
                field,
                &mut memory_layouts,
            )
            .map_err(|e| format!("{}: {e}", function.name))?;
        }
        Ok(CheckedProgram {
            program: self,
            field,
            inputs,
            outputs,
            memory_layouts,
            map_indexes,
        })
    }
}

// Intra-function control flow is forward-only; recursion uses an explicit VM
// call stack. A forward dataflow pass checks initialization on every path.
#[allow(clippy::too_many_arguments)]
fn check_function(
    f: &Function,
    input: usize,
    output: usize,
    inputs: &[Layout],
    outputs: &[Layout],
    enums: &[Enum],
    field: PrimeField,
    layouts: &mut HashMap<Type, Layout>,
) -> Result<(), String> {
    if input > f.registers || f.code.is_empty() {
        return Err("missing input registers or empty code".into());
    }
    let mut states: Vec<Option<Vec<bool>>> = vec![None; f.code.len()];
    let mut initial = vec![false; f.registers];
    initial[..input].fill(true);
    states[0] = Some(initial);
    for (pc, instruction) in f.code.iter().enumerate() {
        let Some(mut initialized) = states[pc].take() else {
            continue;
        };
        let mut reads = vec![];
        let mut writes = vec![];
        let mut successors = vec![pc + 1];
        use Instruction::*;
        match instruction {
            Literal { dest, value } => {
                if !field.contains(*value) {
                    return Err("noncanonical literal".into());
                }
                writes.push(*dest);
            }
            Copy { dest, source } => {
                if dest.len() != source.len() {
                    return Err("copy width mismatch".into());
                }
                reads.extend(source);
                writes.extend(dest);
            }
            Neg { dest, source } => {
                reads.push(*source);
                writes.push(*dest);
            }
            Binary {
                dest, left, right, ..
            } => {
                reads.extend([left, right]);
                writes.push(*dest);
            }
            Guard { tests, .. } | Branch { tests, .. } => {
                for (reg, value) in tests {
                    if !field.contains(*value) {
                        return Err("noncanonical pattern literal".into());
                    }
                    reads.push(*reg);
                }
                if let Branch { otherwise, tests } = instruction
                    && !tests.is_empty()
                {
                    successors.push(*otherwise);
                }
            }
            Jump { target } => {
                successors = vec![*target];
            }
            Call {
                function,
                args,
                dest,
            } => {
                if inputs
                    .get(*function)
                    .is_none_or(|l| l.width() != args.len())
                    || outputs
                        .get(*function)
                        .is_none_or(|l| l.width() != dest.len())
                {
                    return Err("call interface mismatch".into());
                }
                reads.extend(args);
                writes.extend(dest);
            }
            Store {
                r#type,
                value,
                dest,
            } => {
                let layout = r#type.layout(enums, &mut vec![])?;
                if layout.width() != value.len() {
                    return Err("store width mismatch".into());
                }
                layouts.insert(r#type.clone(), layout);
                reads.extend(value);
                writes.push(*dest);
            }
            Load {
                r#type,
                pointer,
                dest,
            } => {
                let layout = r#type.layout(enums, &mut vec![])?;
                if layout.width() != dest.len() {
                    return Err("load width mismatch".into());
                }
                layouts.insert(r#type.clone(), layout);
                reads.push(*pointer);
                writes.extend(dest);
            }
            Hint {
                r#type,
                key_type,
                key,
                dest,
            } => {
                let layout = r#type.layout(enums, &mut vec![])?;
                if !layout.pointer_free()
                    || layout.width() != dest.len()
                    || key_type.layout(enums, &mut vec![])?.width() != key.len()
                {
                    return Err("invalid hint type or width".into());
                }
                reads.extend(key);
                writes.extend(dest);
            }
            AssertEq { left, right, .. } => {
                if left.len() != right.len() {
                    return Err("assertion width mismatch".into());
                }
                reads.extend(left);
                reads.extend(right);
            }
            Ret { value } => {
                if value.len() != output {
                    return Err("return width mismatch".into());
                }
                reads.extend(value);
                successors.clear();
            }
            Fail { .. } => {
                successors.clear();
            }
        }
        for reg in reads {
            if initialized.get(reg) != Some(&true) {
                return Err(format!("instruction {pc} reads undefined register {reg}"));
            }
        }
        for reg in writes {
            *initialized
                .get_mut(reg)
                .ok_or("destination register out of bounds")? = true;
        }
        for next in successors {
            if next <= pc || next >= f.code.len() {
                return Err(format!(
                    "invalid forward jump/fallthrough from {pc} to {next}"
                ));
            }
            match &mut states[next] {
                None => states[next] = Some(initialized.clone()),
                Some(state) => {
                    for (old, new) in state.iter_mut().zip(&initialized) {
                        *old &= new;
                    }
                }
            }
        }
    }
    Ok(())
}
