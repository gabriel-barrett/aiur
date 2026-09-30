import Aiur.Modules
import Aiur.Library.Carry
import Mathlib.Algebra.Field.Rat

/-!
Circuit-only adaptation of Ix/IxVM/Blake3.lean and its ByteStream helpers.
Run with lake exe blake3_stats, or lake env lean --run Examples/Blake3.lean.
No evaluator, hint provider, witness generator, or external I/O is used.
-/

namespace Blake3Example
open Aiur

set_option maxRecDepth 100000
set_option maxHeartbeats 80000000

/-- Empty table declarations make the source readable. The complete generated
rows are installed below, before preparation and either circuit compiler. -/
def declarations : Modules.Program Nat := aiur% "
module U8 {
    type Byte = Field;

    table byte_inputs: (Field,) {}
    table byte_values: Field {}
    table pair_inputs: (Field, Field) {}
    table pair_xors: Field {}
    table pair_sums: Field {}
    table pair_differences: Field {}
    table pair_products: (Field, Field) {}
    table pair_xor_parts4: (Field, Field) {}
    table pair_xor_parts7: (Field, Field) {}
    table pair_units: () {}
    table sum_inputs: (Field,) {}
    table sum_bytes: Field {}

    // Raw maps accept fields. Their tables determine the accepted input domain
    // and establish byte results; a missing input makes the lookup fail.
    map from_field(x: Field) -> Byte = byte_inputs => byte_values;
    map range_pair(a: Field, b: Field) -> () = pair_inputs => pair_units;
    map raw_xor(a: Field, b: Field) -> Byte = pair_inputs => pair_xors;
    map raw_add(a: Field, b: Field) -> Byte = pair_inputs => pair_sums;
    map raw_sub(a: Field, b: Field) -> Byte = pair_inputs => pair_differences;
    map raw_mul(a: Field, b: Field) -> (Byte, Byte) = pair_inputs => pair_products;
    map raw_xor_split4(a: Field, b: Field) -> (Byte, Byte) = pair_inputs => pair_xor_parts4;
    map raw_xor_split7(a: Field, b: Field) -> (Byte, Byte) = pair_inputs => pair_xor_parts7;
    map raw_sum_byte(sum: Field) -> Byte = sum_inputs => sum_bytes;

    // The typed interface delegates to exactly the same lookup after inlining.
    // Byte remains transparent for now; future opacity will hide its construction.
    inline fn to_field(byte: Byte) -> Field { byte }
    inline fn xor(a: Byte, b: Byte) -> Byte { raw_xor(to_field(a), to_field(b)) }
    inline fn add(a: Byte, b: Byte) -> Byte { raw_add(to_field(a), to_field(b)) }
    inline fn sub(a: Byte, b: Byte) -> Byte { raw_sub(to_field(a), to_field(b)) }
    inline fn mul(a: Byte, b: Byte) -> (Byte, Byte) { raw_mul(to_field(a), to_field(b)) }
    inline fn xor_split4(a: Byte, b: Byte) -> (Byte, Byte) {
        raw_xor_split4(to_field(a), to_field(b))
    }
    inline fn xor_split7(a: Byte, b: Byte) -> (Byte, Byte) {
        raw_xor_split7(to_field(a), to_field(b))
    }
    inline fn split_sum(sum: Field) -> (Byte, Field) {
        let byte = raw_sum_byte(sum);
        (byte, (sum - to_field(byte)) / 256)
    }
}

module Words {
    type U32 = [U8::Byte; 4];
    type U64 = [U8::Byte; 8];
    type RawU32 = [Field; 4];

    // Raw word operands need no preliminary checked conversion. The maps check
    // each operation's own domain. For byte operands, sums are in 0..767.
    // The table gives the byte; the input and byte determine the carry.
    inline fn add(a: RawU32, b: RawU32) -> U32 {
        let (s0, c1) = U8::split_sum(a[0] + b[0]);
        let (s1, c2) = U8::split_sum(a[1] + b[1] + c1);
        let (s2, c3) = U8::split_sum(a[2] + b[2] + c2);
        let (s3, _) = U8::split_sum(a[3] + b[3] + c3);
        [s0, s1, s2, s3]
    }

    inline fn add3(a: RawU32, b: RawU32, c: RawU32) -> U32 {
        let (s0, c1) = U8::split_sum(a[0] + b[0] + c[0]);
        let (s1, c2) = U8::split_sum(a[1] + b[1] + c[1] + c1);
        let (s2, c3) = U8::split_sum(a[2] + b[2] + c[2] + c2);
        let (s3, _) = U8::split_sum(a[3] + b[3] + c[3] + c3);
        [s0, s1, s2, s3]
    }

    inline fn xor(a: RawU32, b: RawU32) -> U32 {
        [U8::raw_xor(a[0], b[0]), U8::raw_xor(a[1], b[1]),
         U8::raw_xor(a[2], b[2]), U8::raw_xor(a[3], b[3])]
    }

    inline fn rotr16(w: U32) -> U32 { [w[2], w[3], w[0], w[1]] }
    inline fn rotr8(w: U32) -> U32 { [w[1], w[2], w[3], w[0]] }

    inline fn xor_rotr12(a: RawU32, b: RawU32) -> U32 {
        let (h0, l0) = U8::raw_xor_split4(a[0], b[0]);
        let (h1, l1) = U8::raw_xor_split4(a[1], b[1]);
        let (h2, l2) = U8::raw_xor_split4(a[2], b[2]);
        let (h3, l3) = U8::raw_xor_split4(a[3], b[3]);
        [h1 + l2, h2 + l3, h3 + l0, h0 + l1]
    }

    inline fn xor_rotr7(a: RawU32, b: RawU32) -> U32 {
        let (h0, l0) = U8::raw_xor_split7(a[0], b[0]);
        let (h1, l1) = U8::raw_xor_split7(a[1], b[1]);
        let (h2, l2) = U8::raw_xor_split7(a[2], b[2]);
        let (h3, l3) = U8::raw_xor_split7(a[3], b[3]);
        [h0 + l1, h1 + l2, h2 + l3, h3 + l0]
    }

    fn u64_is_zero(x: U64) -> Field {
        match x { [0, 0, 0, 0, 0, 0, 0, 0] => 1, _ => 0 }
    }

    fn u64_succ(x: U64) -> U64 {
        let (b0, c1) = U8::split_sum(x[0] + 1);
        let (b1, c2) = U8::split_sum(x[1] + c1);
        let (b2, c3) = U8::split_sum(x[2] + c2);
        let (b3, c4) = U8::split_sum(x[3] + c3);
        let (b4, c5) = U8::split_sum(x[4] + c4);
        let (b5, c6) = U8::split_sum(x[5] + c5);
        let (b6, c7) = U8::split_sum(x[6] + c6);
        let (b7, _) = U8::split_sum(x[7] + c7);
        [b0, b1, b2, b3, b4, b5, b6, b7]
    }
}

module Blake3 {
    type Word = Words::U32;
    type RawWord = Words::RawU32;
    type Digest = [Word; 8];
    type Block = [Word; 16];
    type State = [RawWord; 32];
    type ByteStream = &ByteNode;
    type Layer = &LayerNode;

    enum ByteNode { Nil, Cons(U8::Byte, ByteStream) }
    enum LayerNode { Push(Layer, Digest), Nil }
    enum MaybeDigest { None, Some(Digest) }

    const IV = [
        [103, 230, 9, 106], [133, 174, 103, 187],
        [114, 243, 110, 60], [58, 245, 79, 165],
        [127, 82, 14, 81], [140, 104, 5, 155],
        [171, 217, 131, 31], [25, 205, 224, 91]
    ];
    const CHUNK_START = 1;
    const CHUNK_END = 2;
    const PARENT = 4;
    const ROOT = 8;

    fn eq_zero(x: Field) -> Field { match x { 0 => 1, _ => 0 } }

    fn is_empty(input: ByteStream) -> Field {
        match *input { ByteNode::Nil => 1, _ => 0 }
    }

    inline fn hash(input: ByteStream) -> Digest {
        compress_layer(compress_chunks(input, &ByteNode::Nil, 0, 0,
            &[0; 8], &IV, &LayerNode::Nil))
    }

    fn next_layer(layer: Layer, digest: Digest, root: Field) -> (MaybeDigest, Layer) {
        match *layer {
            LayerNode::Nil => (MaybeDigest::Some(digest), layer),
            LayerNode::Push(layer, other) => {
                let (last, new_layer) = next_layer(layer, other, 0);
                match last {
                    MaybeDigest::None => (MaybeDigest::Some(digest), new_layer),
                    MaybeDigest::Some(last) => {
                        let blocks = [
                            last[0], last[1], last[2], last[3],
                            last[4], last[5], last[6], last[7],
                            digest[0], digest[1], digest[2], digest[3],
                            digest[4], digest[5], digest[6], digest[7]
                        ];
                        match *new_layer {
                            LayerNode::Nil => {
                                let result = compress_init(IV, blocks, [0; 8], 64, PARENT + ROOT * root);
                                (MaybeDigest::None, &LayerNode::Push(new_layer, result))
                            },
                            _ => {
                                let result = compress_init(IV, blocks, [0; 8], 64, PARENT);
                                (MaybeDigest::None, &LayerNode::Push(new_layer, result))
                            },
                        }
                    },
                }
            },
        }
    }

    fn compress_layer(layer: Layer) -> Digest {
        let LayerNode::Push(rest, digest) = *layer;
        match *rest {
            LayerNode::Nil => digest,
            _ => {
                let (last, new_layer) = next_layer(rest, digest, 1);
                match last {
                    MaybeDigest::None => compress_layer(new_layer),
                    MaybeDigest::Some(last) => compress_layer(&LayerNode::Push(new_layer, last)),
                }
            },
        }
    }

    fn compress_chunks(
        input: ByteStream, byte_acc: ByteStream,
        block_index: Field, chunk_index: Field,
        chunk_count: &Words::U64, block_digest: &Digest, layer: Layer
    ) -> Layer {
        match *input {
            ByteNode::Nil => finish(byte_acc, block_index, chunk_index, chunk_count, block_digest, layer),
            ByteNode::Cons(head, input) => {
                let byte_acc = &ByteNode::Cons(head, byte_acc);
                match block_index {
                    63 => compress_block(input, byte_acc, chunk_index, chunk_count, block_digest, layer),
                    _ => compress_chunks(input, byte_acc, block_index + 1, chunk_index + 1,
                                         chunk_count, block_digest, layer),
                }
            },
        }
    }

    // The list is reversed: its first element is the last byte of the block.
    fn bytes_to_block(acc: ByteStream) -> Block {
        let ByteNode::Cons(b63, rest) = *acc;
        let ByteNode::Cons(b62, rest) = *rest;
        let ByteNode::Cons(b61, rest) = *rest;
        let ByteNode::Cons(b60, rest) = *rest;
        let ByteNode::Cons(b59, rest) = *rest;
        let ByteNode::Cons(b58, rest) = *rest;
        let ByteNode::Cons(b57, rest) = *rest;
        let ByteNode::Cons(b56, rest) = *rest;
        let ByteNode::Cons(b55, rest) = *rest;
        let ByteNode::Cons(b54, rest) = *rest;
        let ByteNode::Cons(b53, rest) = *rest;
        let ByteNode::Cons(b52, rest) = *rest;
        let ByteNode::Cons(b51, rest) = *rest;
        let ByteNode::Cons(b50, rest) = *rest;
        let ByteNode::Cons(b49, rest) = *rest;
        let ByteNode::Cons(b48, rest) = *rest;
        let ByteNode::Cons(b47, rest) = *rest;
        let ByteNode::Cons(b46, rest) = *rest;
        let ByteNode::Cons(b45, rest) = *rest;
        let ByteNode::Cons(b44, rest) = *rest;
        let ByteNode::Cons(b43, rest) = *rest;
        let ByteNode::Cons(b42, rest) = *rest;
        let ByteNode::Cons(b41, rest) = *rest;
        let ByteNode::Cons(b40, rest) = *rest;
        let ByteNode::Cons(b39, rest) = *rest;
        let ByteNode::Cons(b38, rest) = *rest;
        let ByteNode::Cons(b37, rest) = *rest;
        let ByteNode::Cons(b36, rest) = *rest;
        let ByteNode::Cons(b35, rest) = *rest;
        let ByteNode::Cons(b34, rest) = *rest;
        let ByteNode::Cons(b33, rest) = *rest;
        let ByteNode::Cons(b32, rest) = *rest;
        let ByteNode::Cons(b31, rest) = *rest;
        let ByteNode::Cons(b30, rest) = *rest;
        let ByteNode::Cons(b29, rest) = *rest;
        let ByteNode::Cons(b28, rest) = *rest;
        let ByteNode::Cons(b27, rest) = *rest;
        let ByteNode::Cons(b26, rest) = *rest;
        let ByteNode::Cons(b25, rest) = *rest;
        let ByteNode::Cons(b24, rest) = *rest;
        let ByteNode::Cons(b23, rest) = *rest;
        let ByteNode::Cons(b22, rest) = *rest;
        let ByteNode::Cons(b21, rest) = *rest;
        let ByteNode::Cons(b20, rest) = *rest;
        let ByteNode::Cons(b19, rest) = *rest;
        let ByteNode::Cons(b18, rest) = *rest;
        let ByteNode::Cons(b17, rest) = *rest;
        let ByteNode::Cons(b16, rest) = *rest;
        let ByteNode::Cons(b15, rest) = *rest;
        let ByteNode::Cons(b14, rest) = *rest;
        let ByteNode::Cons(b13, rest) = *rest;
        let ByteNode::Cons(b12, rest) = *rest;
        let ByteNode::Cons(b11, rest) = *rest;
        let ByteNode::Cons(b10, rest) = *rest;
        let ByteNode::Cons(b9, rest) = *rest;
        let ByteNode::Cons(b8, rest) = *rest;
        let ByteNode::Cons(b7, rest) = *rest;
        let ByteNode::Cons(b6, rest) = *rest;
        let ByteNode::Cons(b5, rest) = *rest;
        let ByteNode::Cons(b4, rest) = *rest;
        let ByteNode::Cons(b3, rest) = *rest;
        let ByteNode::Cons(b2, rest) = *rest;
        let ByteNode::Cons(b1, rest) = *rest;
        let ByteNode::Cons(b0, _) = *rest;
        [
            [b0, b1, b2, b3],
            [b4, b5, b6, b7],
            [b8, b9, b10, b11],
            [b12, b13, b14, b15],
            [b16, b17, b18, b19],
            [b20, b21, b22, b23],
            [b24, b25, b26, b27],
            [b28, b29, b30, b31],
            [b32, b33, b34, b35],
            [b36, b37, b38, b39],
            [b40, b41, b42, b43],
            [b44, b45, b46, b47],
            [b48, b49, b50, b51],
            [b52, b53, b54, b55],
            [b56, b57, b58, b59],
            [b60, b61, b62, b63]
        ]
    }

    fn pad_block(acc: ByteStream, n: Field) -> ByteStream {
        match n {
            0 => acc,
            _ => pad_block(&ByteNode::Cons(0, acc), n - 1),
        }
    }

    fn finish(
        byte_acc: ByteStream, block_index: Field, chunk_index: Field,
        chunk_count: &Words::U64, block_digest: &Digest, layer: Layer
    ) -> Layer {
        match (block_index, chunk_index) {
            (0, 0) => {
                match *chunk_count {
                    [0, 0, 0, 0, 0, 0, 0, 0] =>
                        &LayerNode::Push(layer,
                            compress_init(*block_digest, [[0; 4]; 16], *chunk_count,
                                          0, ROOT + CHUNK_START + CHUNK_END)),
                    _ => layer,
                }
            },
            (0, _) => &LayerNode::Push(layer, *block_digest),
            _ => {
                let flags = CHUNK_END + Words::u64_is_zero(*chunk_count) * ROOT
                          + eq_zero(chunk_index - block_index) * CHUNK_START;
                let block = bytes_to_block(pad_block(byte_acc, 64 - block_index));
                &LayerNode::Push(layer, compress_init(*block_digest, block, *chunk_count, block_index, flags))
            },
        }
    }

    fn compress_block(
        input: ByteStream, byte_acc: ByteStream, chunk_index: Field,
        chunk_count: &Words::U64, block_digest: &Digest, layer: Layer
    ) -> Layer {
        let block = bytes_to_block(byte_acc);
        match chunk_index {
            1023 => {
                let flags = ROOT * is_empty(input) * Words::u64_is_zero(*chunk_count) + CHUNK_END;
                let layer = &LayerNode::Push(layer, compress_init(*block_digest, block, *chunk_count, 64, flags));
                compress_chunks(input, &ByteNode::Nil, 0, 0,
                    &Words::u64_succ(*chunk_count), &IV, layer)
            },
            _ => {
                let flags = is_empty(input) * CHUNK_END
                          + is_empty(input) * Words::u64_is_zero(*chunk_count) * ROOT
                          + eq_zero(chunk_index - 63) * CHUNK_START;
                let digest = compress_init(*block_digest, block, *chunk_count, 64, flags);
                compress_chunks(input, &ByteNode::Nil, 0, chunk_index + 1, chunk_count, &digest, layer)
            },
        }
    }

    inline fn g(a: RawWord, b: RawWord, c: RawWord, d: RawWord, x: RawWord, y: RawWord) -> [Word; 4] {
        let a = Words::add3(a, b, x);
        let d = Words::rotr16(Words::xor(d, a));
        let c = Words::add(c, d);
        let b = Words::xor_rotr12(b, c);
        let a = Words::add3(a, b, y);
        let d = Words::rotr8(Words::xor(d, a));
        let c = Words::add(c, d);
        let b = Words::xor_rotr7(b, c);
        [a, b, c, d]
    }

    inline fn round(state: State) -> State {
        let [a, b, c, d] = g(state[0], state[4], state[8], state[12], state[16], state[17]);
        let state = state with { [0] = a, [4] = b, [8] = c, [12] = d };
        let [a, b, c, d] = g(state[1], state[5], state[9], state[13], state[18], state[19]);
        let state = state with { [1] = a, [5] = b, [9] = c, [13] = d };
        let [a, b, c, d] = g(state[2], state[6], state[10], state[14], state[20], state[21]);
        let state = state with { [2] = a, [6] = b, [10] = c, [14] = d };
        let [a, b, c, d] = g(state[3], state[7], state[11], state[15], state[22], state[23]);
        let state = state with { [3] = a, [7] = b, [11] = c, [15] = d };
        let [a, b, c, d] = g(state[0], state[5], state[10], state[15], state[24], state[25]);
        let state = state with { [0] = a, [5] = b, [10] = c, [15] = d };
        let [a, b, c, d] = g(state[1], state[6], state[11], state[12], state[26], state[27]);
        let state = state with { [1] = a, [6] = b, [11] = c, [12] = d };
        let [a, b, c, d] = g(state[2], state[7], state[8], state[13], state[28], state[29]);
        let state = state with { [2] = a, [7] = b, [8] = c, [13] = d };
        let [a, b, c, d] = g(state[3], state[4], state[9], state[14], state[30], state[31]);
        state with { [3] = a, [4] = b, [9] = c, [14] = d }
    }

    inline fn compress_init(cv: Digest, block: Block, counter: Words::U64,
                            block_len: Field, flags: Field) -> Digest {
        let state: State = [
            cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
            IV[0], IV[1], IV[2], IV[3], counter[0..4], counter[4..8],
            [block_len, 0, 0, 0], [flags, 0, 0, 0],
            block[0], block[1], block[2], block[3],
            block[4], block[5], block[6], block[7],
            block[8], block[9], block[10], block[11],
            block[12], block[13], block[14], block[15]
        ];
        compress(0, state)
    }

    fn compress(stage: Field, state: State) -> Digest {
        match stage {
            7 => [
                Words::xor(state[0], state[8]), Words::xor(state[1], state[9]),
                Words::xor(state[2], state[10]), Words::xor(state[3], state[11]),
                Words::xor(state[4], state[12]), Words::xor(state[5], state[13]),
                Words::xor(state[6], state[14]), Words::xor(state[7], state[15])
            ],
            _ => {
                let next = round(state);
                let next = next with {
                    [16] = state[18], [17] = state[22], [18] = state[19], [19] = state[26],
                    [20] = state[23], [21] = state[16], [22] = state[20], [23] = state[29],
                    [24] = state[17], [25] = state[27], [26] = state[28], [27] = state[21],
                    [28] = state[25], [29] = state[30], [30] = state[31], [31] = state[24]
                };
                compress(stage + 1, next)
            },
        }
    }
}

module Benchmark {
    // A deterministic 0,1,...,255,0,... byte stream, constructed inside Aiur.
    fn generate(length: Field, byte: U8::Byte) -> Blake3::ByteStream {
        match length {
            0 => &Blake3::ByteNode::Nil,
            _ => {
                let (next, _) = U8::split_sum(byte + 1);
                let tail = generate(length - 1, next);
                &Blake3::ByteNode::Cons(byte, tail)
            },
        }
    }

    fn main() -> Blake3::Digest { Blake3::hash(generate(1025, 0)) }
}
"

/-- Full byte-pair tables, sharing one input trace across the operations from
ix's `Bytes2` gadget. Output traces have the same order: row `256*a + b`.
The separate sum table provides one byte; an affine expression recovers its carry. -/
def u8Tables : List (Generic.Table Nat) :=
  let byteInputs := (List.range 256).map fun n => Generic.Expr.tuple [.literal n]
  let pairs := (List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)
  let sums := Library.Carry.rows 256 768
  [
    ⟨"byte_inputs", .tuple [.field], byteInputs⟩,
    ⟨"byte_values", .field, (List.range 256).map (.literal ·)⟩,
    ⟨"pair_inputs", .tuple [.field, .field],
      pairs.map fun (a, b) => .tuple [.literal a, .literal b]⟩,
    ⟨"pair_xors", .field, pairs.map fun (a, b) => .literal (Nat.xor a b)⟩,
    ⟨"pair_sums", .field, pairs.map fun (a, b) => .literal ((a + b) % 256)⟩,
    ⟨"pair_differences", .field, pairs.map fun (a, b) => .literal ((a + 256 - b) % 256)⟩,
    ⟨"pair_products", .tuple [.field, .field], pairs.map fun (a, b) =>
      .tuple [.literal ((a * b) % 256), .literal ((a * b) / 256)]⟩,
    ⟨"pair_xor_parts4", .tuple [.field, .field], pairs.map fun (a, b) =>
      let x := Nat.xor a b
      .tuple [.literal (x / 16), .literal ((x % 16) * 16)]⟩,
    ⟨"pair_xor_parts7", .tuple [.field, .field], pairs.map fun (a, b) =>
      let x := Nat.xor a b
      .tuple [.literal (x / 128), .literal ((x % 128) * 2)]⟩,
    ⟨"pair_units", .tuple [], pairs.map fun _ => .tuple []⟩,
    ⟨"sum_inputs", .tuple [.field], sums.map fun (n, _) => .tuple [.literal n]⟩,
    ⟨"sum_bytes", .field, sums.map fun (_, byte) => .literal byte⟩
  ]

def source : Modules.Program Nat :=
  { declarations with modules := declarations.modules.map fun m =>
      if m.name == "U8" then
        { m with body := match m.body with
          | .definitions d => .definitions { d with program.tables := u8Tables }
          | body => body }
      else m }

private def get {α : Type} : Except String α → IO α
  | .ok x => pure x
  | .error e => throw (IO.userError e)

private def ensure (message : String) (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error message

private def tableRows (name : String) : Except String (Array (Generic.Expr Nat)) := do
  let some table := u8Tables.find? (·.name == name) | throw s!"missing generated table {name}"
  return table.rows.toArray

private def scalar : Generic.Expr Nat → Except String Nat
  | .literal n => .ok n
  | _ => .error "expected a generated scalar"

private def pair : Generic.Expr Nat → Except String (Nat × Nat)
  | .tuple [.literal a, .literal b] => .ok (a, b)
  | _ => .error "expected a generated pair"

/-- Check the actual generated rows, including alignment of every output trace,
for all 65,536 byte pairs. This is host-side validation, not Aiur execution. -/
def checkU8Tables : Except String Unit := do
  let byteInputs ← tableRows "byte_inputs"
  let values ← (← tableRows "byte_values").mapM scalar
  let inputs ← (← tableRows "pair_inputs").mapM pair
  let xors ← (← tableRows "pair_xors").mapM scalar
  let adds ← (← tableRows "pair_sums").mapM scalar
  let subs ← (← tableRows "pair_differences").mapM scalar
  let muls ← (← tableRows "pair_products").mapM pair
  let parts4 ← (← tableRows "pair_xor_parts4").mapM pair
  let parts7 ← (← tableRows "pair_xor_parts7").mapM pair
  let units ← tableRows "pair_units"
  let sumInputs ← tableRows "sum_inputs"
  let sums ← (← tableRows "sum_bytes").mapM scalar
  ensure "incomplete byte tables" (byteInputs.size == 256 && values.size == 256)
  ensure "incomplete byte-pair tables" ([inputs.size, xors.size, adds.size, subs.size,
    muls.size, parts4.size, parts7.size, units.size].all (· == 65536))
  ensure "incomplete carry table" (sumInputs.size == 768 && sums.size == 768)
  for n in List.range 256 do
    ensure "byte table alignment" (byteInputs[n]! == .tuple [.literal n] && values[n]! == n)
  for n in List.range 768 do
    let byte := sums[n]!
    ensure "carry table alignment" (sumInputs[n]! == .tuple [.literal n])
    ensure "carry decomposition" (byte < 256 && n / 256 < 3 && byte + 256 * (n / 256) == n)
    ensure "field carry reconstruction" (((n : Rat) - byte) / 256 == (n / 256 : Nat))
  for a in List.range 256 do
    for b in List.range 256 do
      let index := 256 * a + b
      ensure "byte-pair table alignment" (inputs[index]! == (a, b))
      let x := xors[index]!
      ensure "byte XOR" (x == Nat.xor a b)
      ensure "wrapping byte addition" (adds[index]! < 256 &&
        adds[index]! + 256 * ((a + b) / 256) == a + b)
      ensure "wrapping byte subtraction" (subs[index]! < 256 &&
        subs[index]! + b == a + if a < b then 256 else 0)
      let (lo, hi) := muls[index]!
      ensure "byte multiplication" (lo < 256 && hi < 256 && lo + 256 * hi == a * b)
      let (hi, shifted) := parts4[index]!
      ensure "XOR four-bit split" (hi < 16 && shifted < 256 && shifted % 16 == 0 &&
        16 * hi + shifted / 16 == x)
      let (hi, shifted) := parts7[index]!
      ensure "XOR seven-bit split" (hi < 2 && shifted < 256 && shifted % 2 == 0 &&
        128 * hi + shifted / 2 == x)
      ensure "byte-pair range check" (units[index]! == .tuple [])

structure Totals where
  chips : Nat
  columns : Nat
  degree : Nat
  calls : Nat
  rom : Nat
  lookupDegree : Nat
  deriving Repr, BEq

def totals (system : Circuit.System F) : Totals :=
  system.stats.foldl (fun acc s => {
    chips := acc.chips + 1
    columns := acc.columns + s.columns
    degree := max acc.degree s.maxConstraintDegree
    calls := acc.calls + s.callLookups
    rom := acc.rom + s.romLookups
    lookupDegree := max acc.lookupDegree s.maxLookupDegree
  }) ⟨0, 0, 0, 0, 0, 0⟩

def report : IO Unit := do
  get checkU8Tables
  IO.println "Preparing the Blake3 example and generated U8 tables..."
  let prepared ← get <| Modules.prepare (source.toField Rat) ["Benchmark::main"]
  -- Both compilers use this exact same specialization and inline configuration.
  let specialized ← get <| Generic.specialize prepared.environment.source prepared.entries
  IO.println "Compiling the reference circuit..."
  let reference ← get specialized.compile
  IO.println "Compiling the optimized circuit (degree cap 3)..."
  let optimized ← get specialized.compileOptimized
  get <| ensure "compilers received different programs" (reference.program == optimized.inlined.program)
  get <| ensure "precommitted data changed" (reference.system.tables == optimized.system.tables &&
    reference.system.maps == optimized.system.maps)
  -- Every original chip remains explainable, including under deduplication.
  for chip in reference.system.chips do
    let representative := ((optimized.artifact.representatives.find? (·.1 == chip.name)).map Prod.snd).getD chip.name
    let some other := optimized.system.findChip? representative |
      throw (IO.userError s!"missing optimized chip for {chip.name}")
    get <| ensure s!"lookup merging added slots in {chip.name}"
      (other.sends.length ≤ chip.sends.length && other.memory.length ≤ chip.memory.length)
  IO.println "\nReference chips:"
  reference.system.printStats
  IO.println "\nOptimized chips:"
  optimized.system.printStats
  IO.println "\nTotals (sum of static chip widths and lookup slots, not execution cost):"
  let before := totals reference.system
  let after := totals optimized.system
  IO.println "| Metric | Reference | Optimized |"
  IO.println "| --- | ---: | ---: |"
  for (label, a, b) in [
      ("Chips", before.chips, after.chips),
      ("Sum of chip columns", before.columns, after.columns),
      ("Maximum constraint degree", before.degree, after.degree),
      ("Call/map lookup slots", before.calls, after.calls),
      ("ROM lookup slots", before.rom, after.rom),
      ("Maximum lookup expression degree", before.lookupDegree, after.lookupDegree)] do
    IO.println s!"| {label} | {a} | {b} |"
  IO.println "\nShared precommitted tables (separate from chip columns):"
  let mut tableRows := 0
  let mut tableCells := 0
  for table in optimized.system.tables do
    let layout ← get <| (optimized.system.enums.layout table.rowType).mapError reprStr
    IO.println s!"{table.name}: rows={table.rows.length}, width={layout.width}"
    tableRows := tableRows + table.rows.length
    tableCells := tableCells + table.rows.length * layout.width
  IO.println s!"Shared table totals: {tableRows} rows, {tableCells} field cells"
  IO.println s!"Static maps: {optimized.system.maps.length}"
  let merged := optimized.artifact.representatives.filter (fun (name, representative) => name != representative)
  IO.println s!"Merged internal chips: {repr merged}"
  IO.println "\nEntrypoint: Benchmark::main generates 1,025 bytes, then hashes them."
  IO.println "This report compiles the program; it does not execute Blake3 or construct witnesses."
  IO.println "Entrypoint soundness/completeness, degree bounds, and deduplication are proved; memoized soundness assumes acyclicity."

end Blake3Example

def main : IO Unit := Blake3Example.report
