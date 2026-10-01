//! Memoized evaluation. A query is (callable ID, flat arguments); its first
//! completed output is reused. Counts are integers, never field elements.
use crate::bytecode::{Binary as BinOp, CheckedProgram, Instruction, Type};
use crate::value::Value;
use serde::Serialize;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct QueryInput {
    pub function: usize,
    pub args: Vec<u64>,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct QueryOutput {
    pub output: Vec<u64>,
    pub multiplicity: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
pub struct Cell {
    pub r#type: Type,
    pub value: Vec<u64>,
}
#[derive(Clone, Debug, Serialize)]
pub struct MemoryEntry {
    pub cell: Cell,
    pub multiplicity: u64,
}
#[derive(Clone, Debug)]
pub struct Execution {
    pub output: Vec<u64>,
    pub queries: HashMap<QueryInput, QueryOutput>,
    /// Addresses are indices in this heterogeneous, interned ROM.
    pub memory: Vec<MemoryEntry>,
    pub instructions: u64,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExecutionError {
    pub function: String,
    pub instruction: usize,
    pub message: String,
}
impl fmt::Display for ExecutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at instruction {}: {}",
            self.function, self.instruction, self.message
        )
    }
}
impl std::error::Error for ExecutionError {}

struct Frame {
    query: QueryInput,
    registers: Vec<u64>,
    pc: usize,
    destination: Vec<usize>,
}
struct Machine<'a> {
    program: &'a CheckedProgram,
    frames: Vec<Frame>,
    pending: HashSet<QueryInput>,
    record: Execution,
    memory_index: HashMap<Cell, u64>,
}
impl Frame {
    fn read(&self, regs: &[usize]) -> Vec<u64> {
        regs.iter().map(|r| self.registers[*r]).collect()
    }
    fn write(&mut self, dest: &[usize], values: &[u64]) {
        debug_assert_eq!(dest.len(), values.len());
        for (reg, value) in dest.iter().zip(values) {
            self.registers[*reg] = *value;
        }
    }
}
impl CheckedProgram {
    /// A fresh execution session. No cache or pointer can leak across sessions.
    pub fn execute(&self, entry: &str, args: Vec<u64>) -> Result<Execution, ExecutionError> {
        let error = |message| ExecutionError {
            function: entry.into(),
            instruction: 0,
            message,
        };
        let selected = self.entry(entry).map_err(error)?;
        self.inputs[selected.function]
            .validate(&args, self.field)
            .map_err(error)?;
        Machine {
            program: self,
            frames: vec![],
            pending: HashSet::new(),
            memory_index: HashMap::new(),
            record: Execution {
                output: vec![],
                queries: HashMap::new(),
                memory: vec![],
                instructions: 0,
            },
        }
        .run(QueryInput {
            function: selected.function,
            args,
        })
    }

    pub fn execute_values(&self, entry: &str, args: &[Value]) -> Result<Execution, ExecutionError> {
        let error = |message| ExecutionError {
            function: entry.into(),
            instruction: 0,
            message,
        };
        let selected = self.entry(entry).map_err(error)?;
        if args.len() != selected.inputs.len() {
            return Err(error("entry argument count mismatch".into()));
        }
        let mut flat = vec![];
        for (value, ty) in args.iter().zip(&selected.inputs) {
            flat.extend(ty.flatten(value, self.field).map_err(error)?);
        }
        self.execute(entry, flat)
    }

    pub fn output_value(&self, entry: &str, result: &Execution) -> Result<Value, String> {
        let ty = self
            .entry(entry)?
            .output
            .as_ref()
            .ok_or("entry result contains opaque types or pointers")?;
        ty.unflatten(&result.output, self.field)
    }
}
impl Machine<'_> {
    fn error(&self, message: impl Into<String>) -> ExecutionError {
        let (function, instruction) = self
            .frames
            .last()
            .map(|f| {
                (
                    self.program
                        .callable_name(f.query.function)
                        .unwrap_or("<unknown>")
                        .to_owned(),
                    f.pc,
                )
            })
            .unwrap_or(("<entry>".into(), 0));
        ExecutionError {
            function,
            instruction,
            message: message.into(),
        }
    }

    /// Hit: return the existing output and increment only this query's count.
    /// Miss: start a frame, or resolve a static map. Never cache pending results.
    fn request(
        &mut self,
        query: QueryInput,
        destination: Vec<usize>,
    ) -> Result<Option<Vec<u64>>, ExecutionError> {
        if let Some(output) = self.record.queries.get_mut(&query) {
            output.multiplicity =
                output
                    .multiplicity
                    .checked_add(1)
                    .ok_or_else(|| ExecutionError {
                        function: "<query>".into(),
                        instruction: 0,
                        message: "query multiplicity overflow".into(),
                    })?;
            return Ok(Some(output.output.clone()));
        }
        if self.pending.contains(&query) {
            return Err(self.error("recursive query is already being evaluated"));
        }
        if query.function >= self.program.program.functions.len() {
            let map =
                &self.program.program.maps[query.function - self.program.program.functions.len()];
            let row = self.program.map_indexes[&map.input]
                .get(&query.args)
                .ok_or_else(|| self.error(format!("no table entry for {}", map.name)))?;
            let output = self.program.program.tables[map.output].rows[*row].clone();
            self.record.queries.insert(
                query,
                QueryOutput {
                    output: output.clone(),
                    multiplicity: 1,
                },
            );
            return Ok(Some(output));
        }
        let function = &self.program.program.functions[query.function];
        let mut registers = vec![0; function.registers];
        registers[..query.args.len()].copy_from_slice(&query.args);
        self.pending.insert(query.clone());
        self.frames.push(Frame {
            query,
            registers,
            pc: 0,
            destination,
        });
        Ok(None)
    }

    fn run(mut self, root: QueryInput) -> Result<Execution, ExecutionError> {
        if let Some(output) = self.request(root, vec![])? {
            self.record.output = output;
            return Ok(self.record);
        }
        while !self.frames.is_empty() {
            self.record.instructions = self
                .record
                .instructions
                .checked_add(1)
                .ok_or_else(|| self.error("instruction counter overflow"))?;
            let frame = self.frames.last_mut().unwrap();
            let program = self.program;
            let instruction = &program.program.functions[frame.query.function].code[frame.pc];
            use Instruction::*;
            match instruction {
                Literal { dest, value } => frame.registers[*dest] = *value,
                Copy { dest, source } => {
                    let values = frame.read(source);
                    frame.write(dest, &values);
                }
                Neg { dest, source } => {
                    frame.registers[*dest] = program.field.neg(frame.registers[*source])
                }
                Binary {
                    dest,
                    operator,
                    left,
                    right,
                } => {
                    let (a, b) = (frame.registers[*left], frame.registers[*right]);
                    let result = match operator {
                        BinOp::Add => program.field.add(a, b),
                        BinOp::Sub => program.field.sub(a, b),
                        BinOp::Mul => program.field.mul(a, b),
                        BinOp::Div => match program.field.inverse(b) {
                            Some(inv) => program.field.mul(a, inv),
                            None => return Err(self.error("division by zero")),
                        },
                    };
                    frame.registers[*dest] = result;
                }
                Guard { tests, message } => {
                    if !tests
                        .iter()
                        .all(|(reg, value)| frame.registers[*reg] == *value)
                    {
                        return Err(self.error(message));
                    }
                }
                Branch { tests, otherwise } => {
                    if !tests
                        .iter()
                        .all(|(reg, value)| frame.registers[*reg] == *value)
                    {
                        frame.pc = *otherwise;
                        continue;
                    }
                }
                Jump { target } => {
                    frame.pc = *target;
                    continue;
                }
                Call {
                    function,
                    args,
                    dest,
                } => {
                    let query = QueryInput {
                        function: *function,
                        args: frame.read(args),
                    };
                    let dest = dest.clone();
                    let parent = self.frames.len() - 1;
                    let output = self.request(query, dest.clone())?;
                    self.frames[parent].pc += 1;
                    if let Some(output) = output {
                        self.frames[parent].write(&dest, &output);
                    }
                    continue;
                }
                Store {
                    r#type,
                    value,
                    dest,
                } => {
                    let cell = Cell {
                        r#type: r#type.clone(),
                        value: frame.read(value),
                    };
                    program.memory_layouts[r#type]
                        .validate(&cell.value, program.field)
                        .map_err(|e| self.error(e))?;
                    let address = if let Some(address) = self.memory_index.get(&cell) {
                        *address
                    } else {
                        let address = u64::try_from(self.record.memory.len())
                            .map_err(|_| self.error("ROM address overflow"))?;
                        if address >= program.field.modulus() {
                            return Err(self.error("ROM exceeds field capacity"));
                        }
                        self.memory_index.insert(cell.clone(), address);
                        self.record.memory.push(MemoryEntry {
                            cell,
                            multiplicity: 0,
                        });
                        address
                    };
                    let entry = &mut self.record.memory[address as usize];
                    entry.multiplicity =
                        entry
                            .multiplicity
                            .checked_add(1)
                            .ok_or_else(|| ExecutionError {
                                function: "<ROM>".into(),
                                instruction: 0,
                                message: "ROM multiplicity overflow".into(),
                            })?;
                    self.frames.last_mut().unwrap().registers[*dest] = address;
                }
                Load {
                    r#type,
                    pointer,
                    dest,
                } => {
                    let address = usize::try_from(frame.registers[*pointer])
                        .map_err(|_| self.error("ROM address overflow"))?;
                    let Some(entry) = self.record.memory.get_mut(address) else {
                        return Err(self.error("dangling pointer"));
                    };
                    if entry.cell.r#type != *r#type {
                        return Err(self.error("ROM cell type mismatch"));
                    }
                    entry.multiplicity =
                        entry
                            .multiplicity
                            .checked_add(1)
                            .ok_or_else(|| ExecutionError {
                                function: "<ROM>".into(),
                                instruction: 0,
                                message: "ROM multiplicity overflow".into(),
                            })?;
                    self.frames
                        .last_mut()
                        .unwrap()
                        .write(dest, &entry.cell.value);
                }
                Hint {
                    r#type,
                    key_type,
                    key,
                    ..
                } => {
                    let key = frame.read(key);
                    resolve_hint(r#type, key_type, &key);
                }
                AssertEq {
                    left,
                    right,
                    message,
                } => {
                    if frame.read(left) != frame.read(right) {
                        return Err(
                            self.error(message.as_deref().unwrap_or("equality assertion failed"))
                        );
                    }
                }
                Ret { value } => {
                    let output = frame.read(value);
                    program.outputs[frame.query.function]
                        .validate(&output, program.field)
                        .map_err(|e| self.error(e))?;
                    let frame = self.frames.pop().unwrap();
                    self.pending.remove(&frame.query);
                    self.record.queries.insert(
                        frame.query,
                        QueryOutput {
                            output: output.clone(),
                            multiplicity: 1,
                        },
                    );
                    if let Some(parent) = self.frames.last_mut() {
                        parent.write(&frame.destination, &output);
                    } else {
                        self.record.output = output;
                    }
                    continue;
                }
                Fail { message } => return Err(self.error(message)),
            }
            self.frames.last_mut().unwrap().pc += 1;
        }
        Ok(self.record)
    }
}

/// Key computation is ordinary bytecode execution. Provider policy, including
/// how a future provider interacts with query memoization, is deliberately open.
fn resolve_hint(expected_type: &Type, key_type: &Type, key: &[u64]) -> ! {
    let _ = (expected_type, key_type, key);
    todo!("keyed nondeterminism provider")
}
