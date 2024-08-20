# BaseFloats.jl
### The internal constructive model for MicroFloats.
##### Copyright 2024 by Jeffrey Sarnoff

[![Aqua QA](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)  [![JET](https://img.shields.io/badge/%F0%9F%9B%A9%EF%B8%8F_tested_with-JET.jl-233f9a)](https://github.com/aviatesk/JET.jl)

----

BaseFloats.jl provides the concrete type `BaseFloat`, with the parameters `Bitwidth` and `Precision`.
- const MF32 = BaseFloat(3, 2) # Bitwidth = 3, Precision = 2
- const MF108 = BaseFloat(10, 8) # Bitwidth = 10, Precision = 8

#### The parameters are available
- MF32bitwidth = bitwidth(SMF32)
- MF32precision = precision(SMF32)

A `BaseFloat` contains two fields, `encoding` and `values`.
- `encoding` holds the sequence of value encodings for the specified Bitwidth and Precision
- `values` holds the sequence floating-point values  for the specified Bitwidth and Precision

#### The fields are available
- MF32encoding = encoding(MF32)
- MF32values = values(MF32)

### Technical Notes

#### BaseFloats are used to construct other MicroFloat types
- they are not intended for direct use
  - see UnsignedMicroFloats.jl
  - see SignedMicroFloats.jl

#### The values of a BaseFloat are finite non-negative numbers:
- there is one 0
- there are no negative values
- there are no NaNs
- there are no Infs

#### Types used
```
if the Bitwidth is <= 8
    the encoding is a vector of UInt8
    the values are a vector of Float32
else
    the encoding is a vector of UInt16
    the values are a vector of Float64
end
```

### example
```
using BaseFloat

MF32 = BaseFloat(3, 2);

bitwidth(MF32)
# 3

precision(MF32)
# 2

encoding(MF32)
# [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]

values(MF32)
# [0.0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0]
```
----

## _Symbols Used_


|                  | symbol | meaning                     |   | LaTeX  | Unicode |
|------------------|:------:|:----------------------------|---|:-------|:-------:|
|                  |        |                             |   |        |         |
|                  |        | *membership*                |   |        |         |
|                  |        |                             |   |        |         |
| enfolds          |   ∋    | contains as a member  Set Contains as am element [a Member]    |   | \ni    | U+220B  |
| parthood         |   ∈    | element of   Is an element of [a member of] Set  |   | \in    | U+2208  |
|                  |        |                             |   |        |         |
| enfolds          |   ∋    | Set Contains as a Member    |   | \ni    | U+220B  |
⨃ means "union of sets that are pairwise disjoint"
⨄ means "union of sets that support +" 
| parthood         |   ⋹    | Element of Subset of Set   |   | \in    | U+2208  |
|                  |        |                             |   |        |         |
|                  |        |                             |   |        |         |
|                  |        |  *nonassociation*            |   |        |         |
|                  |        |                             |   |        |         |
| nonparthood      |   ∌    | does not contain as a member   Set Omits as a Member       |   | \notni | U+220C  |
| separateness     |   ∉    | not an elment of   Member is Excluded from Set |   | \notin | U+2209  |
|                  |        |                             |   |        |         |
|                  |   ⋲    | contditionally set contains element   |   |        |  U+22F2   |
|                  |   ⋺    | given condition element is contained in a set  |   |        |  U+22FA   |
|                  |        |  membership in a set is contingent upon constraints (conditional belonging) |                  |        |                             |   |        |         |
|                  |        |                             |   |        |         |
|                  |   ⋳    | special operation akin to "element of set"   |   |        |  U+22F3  |
|                  |   ⋻    | special operation akin to "set econtains as element"  |   |        |  U+22FB   |
|                  |        |                             |   |        |         |
|                  |        |                             |   |        |         |
|                  |        | *precede*                   |   |        |         |
|                  |        |                             |   |        |         |
| enfolds          |   ⊱    | succeeds under relation     |   | \ni    | U+22B1  |
| parthood         |   ⊰    | precedes under relation     |   | \in    | 0x22B0 |
|                  |        |                             |   |        |         |



|              | symbol | meaning                        |   | LaTeX  | Unicode |
|--------------|:------:|:-------------------------------|---|:-------|:-------:|
|              |        |                                |   |        |         |
| *membership* |        |                                |   |        |         |
|              |   ∋    | Set Contains as a Member       |   | \ni    | U+220B  |
|              |   ∋    | Element belongs to Set         |   | \ni    | U+220B  |
|              |   ∌    | Set omits as a Member          |   | \notni | U+220C  |
|              |   ∌    | Element does not belong to Set |   | \notni | U+220C  |
|              |        |                                |   |        |         |
| *parthood*   |        |                                |   |        |         |
|              |   ∈    | Element Is Contained in Set    |   | \in    | U+2208  |
|              |   ∉    | Element is not part of Set     |   | \notin | U+2209  |



U+224D (8781)		≍	EQUIVALENT TO
(mathematics) Of two sets, having a one-to-one correspondence. 
Synonym: equinumerous
(mathematics) Relating to the corresponding elements of an equivalence relation.


U+2258 (8792)		≘	CORRESPONDS TO
