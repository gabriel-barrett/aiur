//! Aiur's untrusted execution engine. Lean supplies execution bytecode; Rust
//! evaluates it and records memoized queries, without generating circuit rows.

pub mod bytecode;
pub mod execute;
mod ffi;
pub mod field;
pub mod hints;
pub mod value;

pub use bytecode::Program;
pub use execute::{Execution, ExecutionError, QueryInput, QueryOutput};
