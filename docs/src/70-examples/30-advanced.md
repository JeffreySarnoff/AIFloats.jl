# [Advanced examples](@id examples-advanced)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

## Pack code points densely

[`PackedVector`](@ref) stores each code point in exactly the format's `K` bits.
Packing is useful when `K` is smaller than the ordinary `UInt8` or `UInt16`
storage unit.

```@example advanced_pack
using AIFloats

T = BinaryValue(Binary5p2se)
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
P = PackedVector(A)

(packing_saves(T), length(P), Base.summarysize(P), collect(P) == A)
```

Packed unary operations return an ordinary vector:

```@example advanced_packed_op
using AIFloats

T = BinaryValue(Binary5p2se)
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
P = PackedVector(A)
F = Binary5p2se
negated = vmap(:Negate, F, RTE_SN, P)
(negated, typeof(negated))
```

Use packed storage to reduce memory traffic or retained size, not automatically
for compute speed; bit extraction has a cost.

### Serialize packed storage portably

`packedwords`/`packedbytes` and their inverses are the wire forms. Both are
*logical* — defined on the bit stream, not on this host's byte order — so what
one machine writes another reads. The byte form is the minimal `cld(n*K, 8)`
bytes and is the shorter of the two whenever the payload does not fill its last
64-bit word:

```@example advanced_pack_wire
using AIFloats

T = BinaryValue(Binary5p2se)
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
P = PackedVector(A)

bytes = AIFloats.packedbytes(P)
back = AIFloats.packedfrombytes(T, bytes, length(A))

(length(bytes), 8 * length(AIFloats.packedwords(P)), collect(back) == A)
```

Both readers validate rather than guess. A reader cannot tell a corrupt stream
from a differently-conventioned writer, so it refuses:

```@example advanced_pack_refuse
using AIFloats

T = BinaryValue(Binary5p2se)
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
bytes = AIFloats.packedbytes(PackedVector(A))

wrong_length = try
    AIFloats.packedfrombytes(T, bytes, length(A) + 50)
catch err
    err
end

corrupt_padding = copy(bytes)
corrupt_padding[end] |= 0x80          # set a bit in the unused high padding
nonzero_padding = try
    AIFloats.packedfrombytes(T, corrupt_padding, length(A))
catch err
    err
end

(wrong_length, nonzero_padding)
```

### Copy packed and block storage

`copy`, `similar`, and an exact-type `copyto!` are defined for both containers.
`similar` returns the *same* concrete container type — packed storage stays
packed, and a `BlockVector` keeps its block size and both formats in its type:

```@example advanced_copying
using AIFloats

T = BinaryValue(Binary5p2se)
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
P = PackedVector(A)

Q = similar(P)
copyto!(Q, P)

(typeof(Q), typeof(Q) === typeof(P), collect(Q) == A, copy(P) !== P)
```

```@example advanced_copying_blocks
using AIFloats

S = Binary8p1uf
E = Binary5p2se
bx = Block(S(1.0), (E(1.5), E(0.25), E(-0.5), E(2.0)))
bv = BlockVector([bx, bx])

bw = similar(bv)
copyto!(bw, bv)

(typeof(bw) === typeof(bv), size(bw), bw[1] == bx)
```

`copyto!` requires the exact element type. A `BlockVector`'s type carries its
block size and both its formats, so a copy between differently shaped
containers cannot type-check rather than silently reshaping.

## Build shared-scale blocks

A [`Block`](@ref) combines one scale datum with a fixed tuple of element datums.

```@example advanced_block
using AIFloats

S = Binary8p1uf   # 8-bit scale, 1 bit of precision
E = Binary5p2se   # 5-bit elements, 2 bits of precision

bx = Block(S(1.0), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(S(1.0), (E(0.5), E(0.75), E(1.0), E(-1.0)))

(blocksize(bx), scaleformat(bx), elemformat(bx))
```

Every registered operation has a generated `Block*` form. The last argument is
the result scale:

```@example advanced_block_add
using AIFloats

S = Binary8p1uf
E = Binary5p2se
bx = Block(S(1.0), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(S(1.0), (E(0.5), E(0.75), E(1.0), E(-1.0)))
bz = BlockAdd(E, RTE_SN, bx, by, S(1.0))
(bz, AIFloats.blockdecode(bz))
```

## Reduce a block with one final projection

Block reductions first try an allocation-free exact accumulator. That fast path
is used only after checking that the decoded lanes are finite, each required
product is represented exactly, and aligning or multiplying the significands
will stay within the accumulator's fixed-width limits. If any check fails, the
operation restarts from the original block values using `BigFloat` at a
precision derived to hold the complete reduction exactly. Thus these checks
affect performance only: both paths form the same exact reduction and project
once into the requested result format.

```@example advanced_reductions
using AIFloats

S = Binary8p1uf
E = Binary5p2se
bx = Block(S(1.0), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(S(1.0), (E(0.5), E(0.75), E(1.0), E(-1.0)))
(
    sum = BlockReduceAdd(E, RTE_SN, bx),
    product = BlockReduceMultiply(E, RTE_SN, bx),
    dot = BlockDotProduct(E, RTE_SN, bx, by),
)
```

All three reductions share the guarded route — including
[`BlockReduceMultiply`](@ref), which has a checked exact fast path like the
others. Its guard simply fails sooner, because accumulating products leaves the
exact fixed-point band quickly, so in practice it reaches the `BigFloat`
fallback more often. Which path ran is not observable in the result, and the
documentation deliberately does not promise a particular carrier for a
particular input — only that both paths form the same exact reduction and
project once.

### Blocks of different widths and precisions

The scale and element formats are independent, and neither has to match the
result format:

```@example advanced_block_mixed
using AIFloats

S = Binary8p1uf          # 8-bit scale, precision 1 — the scale format the
                         # Interim Report requires at its §4.5
E = Binary4p2sf          # 4-bit elements, precision 2
R = Binary8p4se          # a wider, more precise result format

b = Block(S(2.0), (E(1.5), E(0.5), E(-1.0), E(0.25)))

(
    scale = scaleformat(b),
    elements = elemformat(b),
    lanes = AIFloats.blockdecode(b),
    reduced_into_R = BlockReduceAdd(R, RTE_SN, b),
    reduced_into_E = BlockReduceAdd(E, RTE_SN, b),
)
```

## Convert values to and from block form

```@example advanced_block_convert
using AIFloats

S = Binary8p1uf
E = Binary5p2se
values = (E(0.5), E(1.0), E(1.5), E(2.0))
block = ConvertToBlock(E, RTE_SN, values, S(1.0))
roundtrip = ConvertFromBlock(E, RTE_SN, block)
(block, roundtrip)
```

For collections of equally shaped blocks, [`BlockVector`](@ref) uses a
structure-of-arrays layout:

```@example advanced_block_vector
using AIFloats

S = Binary8p1uf
E = Binary5p2se
bx = Block(S(1.0), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(S(1.0), (E(0.5), E(0.75), E(1.0), E(-1.0)))
bz = BlockAdd(E, RTE_SN, bx, by, S(1.0))
blocks = [bx, by, bz]
storage = BlockVector(blocks)
(size(storage), storage[2] == by)
```

Continue with [Technical examples](@ref examples-technical) to inspect policy
and correctness machinery.

```@meta
DocTestSetup = nothing
```
