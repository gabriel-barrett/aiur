# Static tables

Status: design under discussion; not implemented.

## Agreed scope

Aiur will support named tables whose contents are supplied statically as part of
the program. Tables will be generated programmatically, while retaining a
frontend with explicit `table ... { rows }` declarations and ordinary call syntax.
A generator may emit source text or construct an AST that undergoes the same
checks.

For now, both sides of a row are tuples of field elements. Each table has a fixed
input arity and a fixed output arity. Table columns do not contain pointers or
enums. This restriction is to field elements; a byte domain, when wanted, is
established by a particular table's entries.

## Proposed signature and row syntax

Keep the function-like declaration syntax, with field parameters and an explicit
tuple result. Each row supplies the argument tuple and result tuple. For example,
this table contains all rows of XOR on two one-bit inputs:

```rust
table bit_xor(a: Field, b: Field) -> (Field,) {
    (0, 0) => (0,),
    (0, 1) => (1,),
    (1, 0) => (1,),
    (1, 1) => (0,),
}

fn example() -> (Field,) {
    bit_xor(1, 1)
}
```

Rows contain explicit values. Generation loops and computations occur outside
Aiur. The existing field-agnostic frontend convention applies: natural literals
are converted to the selected field, then field-dependent validity is checked.
The proposed initial representation uses flat tuples, one field per column.

## Proposed semantics and proof integration

The initial recommendation is directed lookup: one output tuple per input tuple,
with absent inputs producing an evaluation error. Distinct input tuples may have
the same output. Duplicate input keys would be rejected both before and after
field specialization. This retains deterministic evaluation.

The phrase “tuple <-> tuple relationship” does not yet settle whether reverse
lookup or several outputs for one input should be supported. Those would require
an explicit choice of lookup direction and treatment of ambiguous results; they
are not assumed by this proposal.

A circuit lookup would allocate fresh output columns and require membership of
the full input/output row in the named table, guarded by the current enable.
The table is fixed by the program. Each row provides a reusable rule with no
premises, independently of how many lookups use it. As with ROM lookup, table
membership can be a side condition of a valid chip row, preserving the existing
function-derivation and memoized-graph machinery.

Compiler correctness would relate source lookup to lookup of the same encoded
table. A separate theorem for each generated table can establish that its rows
implement the intended operation, such as byte XOR. No implementation or proof
extension is claimed yet.
