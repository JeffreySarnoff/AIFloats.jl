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

T = binary5p2se
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
P = PackedVector(A)

(packing_saves(T), length(P), Base.summarysize(P), collect(P) == A)
```

Packed unary operations return an ordinary vector:

```@example advanced_packed_op
using AIFloats

T = binary5p2se
A = T[0.0, 0.5, 1.0, 1.5, 2.0, 3.0]
P = PackedVector(A)
F = BinaryFormatOf(T)
negated = vmap(:Negate, F, RTE_SN, P)
(negated, typeof(negated))
```

Use packed storage to reduce memory traffic or retained size, not automatically
for compute speed; bit extraction has a cost.

## Build shared-scale blocks

A [`Block`](@ref) combines one scale datum with a fixed tuple of element datums.

```@example advanced_block
using AIFloats

S = binary8p1uf   # 8-bit scale, 1 bit of precision
E = binary5p2se   # 5-bit elements, 2 bits of precision

bx = Block(one(S), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(one(S), (E(0.5), E(0.75), E(1.0), E(-1.0)))

(blocksize(bx), scaleformat(bx), elemformat(bx))
```

Every registered operation has a generated `Block*` form. The last argument is
the result scale:

```@example advanced_block_add
using AIFloats

S = binary8p1uf
E = binary5p2se
bx = Block(one(S), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(one(S), (E(0.5), E(0.75), E(1.0), E(-1.0)))
bz = BlockAdd(E, RTE_SN, bx, by, one(S))
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

S = binary8p1uf
E = binary5p2se
bx = Block(one(S), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(one(S), (E(0.5), E(0.75), E(1.0), E(-1.0)))
(
    sum = BlockReduceAdd(E, RTE_SN, bx),
    product = BlockReduceMultiply(E, RTE_SN, bx),
    dot = BlockDotProduct(E, RTE_SN, bx, by),
)
```

## Convert values to and from block form

```@example advanced_block_convert
using AIFloats

S = binary8p1uf
E = binary5p2se
values = (E(0.5), E(1.0), E(1.5), E(2.0))
block = ConvertToBlock(E, RTE_SN, values, one(S))
roundtrip = ConvertFromBlock(E, RTE_SN, block)
(block, roundtrip)
```

For collections of equally shaped blocks, [`BlockVector`](@ref) uses a
structure-of-arrays layout:

```@example advanced_block_vector
using AIFloats

S = binary8p1uf
E = binary5p2se
bx = Block(one(S), (E(1.5), E(0.25), E(-0.5), E(2.0)))
by = Block(one(S), (E(0.5), E(0.75), E(1.0), E(-1.0)))
bz = BlockAdd(E, RTE_SN, bx, by, one(S))
blocks = [bx, by, bz]
storage = BlockVector(blocks)
(size(storage), storage[2] == by)
```

Continue with [Technical examples](@ref examples-technical) to inspect policy
and correctness machinery.

```@meta
DocTestSetup = nothing
```
