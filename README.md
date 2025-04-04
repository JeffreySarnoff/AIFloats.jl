# FloatsForML

[![Stable Documentation](https://img.shields.io/badge/docs-stable-blue.svg)](https://DiademSpecialProjects.github.io/FloatsForML.jl/stable)
[![In development documentation](https://img.shields.io/badge/docs-dev-blue.svg)](https://DiademSpecialProjects.github.io/FloatsForML.jl/dev)
[![Build Status](https://github.com/DiademSpecialProjects/FloatsForML.jl/workflows/Test/badge.svg)](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions)
[![Test workflow status](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions/workflows/Test.yml/badge.svg?branch=main)](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions/workflows/Test.yml?query=branch%3Amain)
[![Lint workflow Status](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions/workflows/Lint.yml/badge.svg?branch=main)](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions/workflows/Lint.yml?query=branch%3Amain)
[![Docs workflow Status](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions/workflows/Docs.yml/badge.svg?branch=main)](https://github.com/DiademSpecialProjects/FloatsForML.jl/actions/workflows/Docs.yml?query=branch%3Amain)
[![Coverage](https://codecov.io/gh/DiademSpecialProjects/FloatsForML.jl/branch/main/graph/badge.svg)](https://codecov.io/gh/DiademSpecialProjects/FloatsForML.jl)
[![DOI](https://zenodo.org/badge/DOI/FIXME)](https://doi.org/FIXME)
[![BestieTemplate](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/JuliaBesties/BestieTemplate.jl/main/docs/src/assets/badge.json)](https://github.com/JuliaBesties/BestieTemplate.jl)

## How to Cite

If you use FloatsForML.jl in your work, please cite using the reference given in [CITATION.cff](https://github.com/DiademSpecialProjects/FloatsForML.jl/blob/main/CITATION.cff).
=======
# FloatsForML.jl
### The internal constructive model for MicroFloats.
##### Copyright 2024 by Jeffrey Sarnoff

[![Aqua QA](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)  [![JET](https://img.shields.io/badge/%F0%9F%9B%A9%EF%B8%8F_tested_with-JET.jl-233f9a)](https://github.com/aviatesk/JET.jl)

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
