# Static tables

Status: design under discussion; not implemented.

## Agreed scope

Aiur will support named tables whose contents are supplied statically as part of
the program and precommitted in the eventual SNARK. Operations such as `u8_add`,
`u8_mul`, and `u8_xor` will share one input table and have separate output tables.
Tables will be generated programmatically, while retaining a frontend with
explicit rows and ordinary call syntax. A generator may emit source text or
construct an AST that undergoes the same checks.

For now, inputs and outputs are tuples of field elements. An input table has a
fixed tuple width, and each output table has its own fixed tuple width. Table
columns do not contain pointers or enums. This restriction is to field elements;
a byte domain, when wanted, is established by a particular table's entries.

## Shared inputs and separate outputs

The proposed representation is a family of tables with a common row index:

```text
inputs : Fin N -> Field^m
outputs[operation] : Fin N -> Field^(outputWidth[operation])
```

Each operation references the shared input table and supplies its own output
table. All output tables have exactly the same number of rows as the input
table. Row `i` of an output table is the result for row `i` of the input table.
The input rows are stored once; each operation stores only its outputs and a
reference to the input table. Output widths may differ between operations.

For example, a fragment with singleton outputs could be displayed as follows.
The columns after `inputs` are separate output tables; they are shown together
to make their alignment visible:

| Row | Shared inputs | `u8_add` outputs | `u8_mul` outputs | `u8_xor` outputs |
| --- | --- | --- | --- | --- |
| 0 | `(3, 5)` | `(8,)` | `(15,)` | `(6,)` |
| 1 | `(4, 2)` | `(6,)` | `(8,)` | `(6,)` |

These example rows do not settle overflow conventions. An operation could instead
return a wider tuple, for example a result and a carry. Different output rows
may contain the same value, as in the XOR column above.

For a full binary byte domain, the shared input table contains all 65,536 input
pairs. Every operation supplies one output tuple for each pair. Adding an
operation adds an output table without duplicating the inputs.

## Proposed signature and row syntax

For one operation, keep the proposed function-like declaration syntax, with
field parameters and an explicit tuple result. Each row supplies the argument
tuple and result tuple. For example, this table contains all rows of XOR on two
one-bit inputs:

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

For several operations, a possible extension groups their signatures and rows:

```rust
table u8_ops(a: Field, b: Field) {
    outputs {
        u8_add: (Field,),
        u8_mul: (Field,),
        u8_xor: (Field,),
    }
    rows {
        (3, 5) => {
            u8_add: (8,),
            u8_mul: (15,),
            u8_xor: (6,),
        },
        // The generator supplies all remaining byte input pairs.
    }
}

fn example() -> (Field,) {
    u8_xor(3, 5)
}
```

This is proposed syntax, not a final grammar. Each row specifies its input once
and gives an output for every declared operation. The frontend separates these
into one input table and the aligned output tables. The named braces organize
table declarations; they do not introduce a record value type. A call names one
operation and returns only that operation's output tuple. The single-operation
syntax is shorthand for the same representation with one output table.

Rows contain explicit values. Generation loops and computations occur outside
Aiur. The existing field-agnostic frontend convention applies: natural literals
are converted to the selected field, then field-dependent validity is checked.
The proposed initial representation uses flat tuples, one field per column.

## Proposed semantics and proof integration

The initial recommendation is directed lookup: find the row of the shared input
table matching the arguments, then return the same row of the selected output
table. Absent inputs produce an evaluation error. Duplicate input keys would be
rejected both before and after field specialization. Together with row-count and
width checks, this gives one output tuple per input tuple for each operation and
retains deterministic evaluation. Distinct inputs may have the same output.

The phrase “tuple <-> tuple relationship” does not yet settle whether reverse
lookup or several outputs for one input should be supported. Those would require
an explicit choice of lookup direction and treatment of ambiguous results; they
are not assumed by this proposal.

A circuit lookup would allocate fresh columns for the selected operation's
output and require the following relation, guarded by the current enable:

```text
Lookup(family, operation, args, result) :=
  exists i : Fin N,
    inputs[i] = args and outputs[operation][i] = result
```

Both sides must use the same row index. Independent membership in the input
table and the output table would permit incorrect input/output pairings. This
abstract index need not be a single field element or appear in source values;
its representation and how the backend enforces alignment remain separate
design choices. The selected operation identifies the output table; no opcode
column in the shared input table is required by this model. The lookup need not
witness the outputs of other operations.

The input and output tables are fixed by the program, unlike the prover-chosen
ROM. Each paired input/output row provides a reusable rule with no premises,
independently of how many lookups use it. As with ROM lookup, this relation can
be a side condition of a valid chip row, preserving the existing function
derivation and memoized graph machinery. Defining a relation per operation does
not require materializing a copy of the shared input table per operation.

Compiler correctness would relate source lookup to lookup of the same encoded
table. A separate theorem for each generated table can establish that its rows
implement the intended operation, such as byte XOR. No implementation or proof
extension is claimed yet.

The abstract model preserves shared input identity and operation-specific output
identity. It does not prescribe how their eventual commitments or lookup
arguments are constructed.
