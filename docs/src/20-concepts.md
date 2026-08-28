# [Concepts](@id concepts)

```@meta
CurrentModule = AIFloats
DocTestSetup = :(using AIFloats)
```

Machine learning runs into a wall that general-purpose arithmetic does not: moving weights
and activations costs more than computing with them. The response has been to shrink the
numbers — 8 bits, 6, 4, sometimes fewer. At those widths the design choices IEEE 754 made
for 32- and 64-bit arithmetic stop paying for themselves. A second NaN, a signed zero, or an
exponent range reserved for specials costs a noticeable fraction of everything the format can
say.

**IEEE P3109**, the draft *Standard for Arithmetic Formats for Machine Learning*, is the
response. A P3109 format is completely determined by four parameters, and AIFloats.jl models
exactly those four.

## The four parameters

A [`Binary`](@ref) specifier is written `Binary{K,P,S,D}`.

| | Name | Meaning |
|:--|:--|:--|
| `K` | bitwidth | total bits the format occupies |
| `P` | precision | significand bits, **counting the implicit leading bit** |
| `S` | signedness | [`SIGNED`](@ref) or [`UNSIGNED`](@ref) |
| `D` | domain | [`FINITE`](@ref) or [`EXTENDED`](@ref) |

Nothing else is needed. There is no separate flag for subnormals, no exponent-bits field, no
bias parameter — each follows from these four.

## The bit budget

Every bit is either sign, exponent, or stored significand:

```
K  =  S  +  exponent bits  +  (P - 1)
```

`P - 1` rather than `P` because the leading significand bit is implicit — it is not stored,
so precision always exceeds the stored significand by one. That is what
`AIFloats.TrailingSignificantBitsOf` returns:

```jldoctest concepts
julia> B = Binary(8, 4, SIGNED, FINITE);

julia> PrecisionOf(B), AIFloats.TrailingSignificantBitsOf(B)
(4, 3)
```

Rearranged, the exponent gets whatever is left:

```
exponent bits  =  K - P - S
```

So for the format above: 8 − 4 − 1 = 3 exponent bits, alongside 1 sign bit and 3 stored
significand bits.

### Dropping the sign buys range

An unsigned format spends no bit on sign, so the same `K` and `P` leave it one more exponent
bit — twice the dynamic range, for giving up negative values. That is a real trade for
quantities known to be non-negative, such as post-ReLU activations or attention weights.

| Format | `K` | `P` | sign | exponent | stored significand |
|:--|--:|--:|--:|--:|--:|
| `Binary(8, 4, SIGNED, …)` | 8 | 4 | 1 | 3 | 3 |
| `Binary(8, 4, UNSIGNED, …)` | 8 | 4 | 0 | 4 | 3 |

### Where the validity rules come from

[`Binary`](@ref) rejects combinations that do not describe a format. The rules read directly
off the budget:

- **`P > 0`** — a format needs at least one significand bit.
- **`P <= K - S`** — after the sign bit, at least one bit must be left for the exponent. This
  is the `- S` term: signed formats can reach `P = K - 1`, unsigned formats `P = K`.
- **`K > 2`** — below three bits nothing survives the other two rules.

```jldoctest concepts
julia> Binary(8, 7, SIGNED, FINITE)     # 1 sign + 6 stored + 1 exponent
Binary{8, 7, ±, ⏥}

julia> Binary(8, 8, UNSIGNED, FINITE)   # no sign, so P may reach K
Binary{8, 8, +, ⏥}

julia> Binary(8, 8, SIGNED, FINITE)     # would need 9 bits
ERROR: ArgumentError: Invalid format: K=8, P=8, S=true, D=false
[...]
```

## Signedness

[`SIGNED`](@ref) formats represent negative values; [`UNSIGNED`](@ref) formats represent
magnitudes only.

P3109 formats have a single zero — there is no negative zero. The code point that would
encode −0 in an IEEE 754 layout is put to other use.

## Domain

[`FINITE`](@ref) and [`EXTENDED`](@ref) name which values exist beyond the reals:

| Domain | Value set | Displayed |
|:--|:--|:--|
| [`FINITE`](@ref) | reals ∪ {NaN} | `⏥` |
| [`EXTENDED`](@ref) | reals ∪ {NaN, ±Inf} | `∞` |

!!! warning "\"Extended\" means infinities"
    It does **not** mean extra bits, extra exponent range, or extended precision. An extended
    format is one whose value *domain* has been extended with the infinities — nothing more.
    Choosing `EXTENDED` spends representable values on ±Inf; choosing `FINITE` keeps them for
    finite numbers.

Either way there is exactly one NaN. Where IEEE 754 has millions of NaN payloads, P3109 has
one, and spends the difference on numbers.

## Subnormals are not a parameter

Subnormals follow from `P` alone:

- `P == 1` — no subnormals.
- `P > 1` — gradual underflow, with `2^(P-1) - 1` subnormal magnitudes.

So there is no `has_subnormals` argument to set. Zero together with the subnormal magnitudes
is called the **prenormal** region, and it holds `2^(P-1)` values.

## Naming

P3109 names a format `binary⟨K⟩p⟨P⟩⟨u|s⟩⟨f|e⟩` — bitwidth, `p`, precision, then `u`/`s` for
unsigned/signed and `f`/`e` for finite/extended. Each name maps one-to-one onto a `Binary`:

| P3109 name | AIFloats.jl |
|:--|:--|
| `binary8p4sf` | `Binary(8, 4, SIGNED, FINITE)` |
| `binary8p4se` | `Binary(8, 4, SIGNED, EXTENDED)` |
| `binary8p4uf` | `Binary(8, 4, UNSIGNED, FINITE)` |
| `binary4p2ue` | `Binary(4, 2, UNSIGNED, EXTENDED)` |

## Compared with IEEE 754

| | IEEE 754 | P3109 |
|:--|:--|:--|
| Smallest standard width | 16 bits | a handful of bits (this package: `K > 2`) |
| Zeros | +0 and −0 | one zero |
| NaNs | many payloads | exactly one |
| Infinities | always present | only when `EXTENDED` |
| Subnormals | always | when `P > 1` |

The IEEE 754 binary formats are available under their standard names —
[`binary16`](@ref), [`binary32`](@ref), [`binary64`](@ref), [`binary128`](@ref) — along with
[`bfloat16`](@ref), so they can be referred to the same way.

```@meta
DocTestSetup = nothing
```
