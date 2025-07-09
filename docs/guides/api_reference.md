# AIFloats.jl API Reference

## Constructor Functions

### `AIFloat`

```julia
AIFloat(T::Type{<:AbstractAIFloat}) -> struct <AIFloat>

AIFloat(bitwidth::Int, sigbits::Int, {:signed, :unsigned}, {:finite, :extended}) -> struct <AIFloat>
```

Create an AIFloat format with specified parameters.

**Parameters:**
- `bitwidth`: Total number of bits (2-15)
- `sigbits`: Number of significand bits (1 to bitwidth-1 for signed, 1 to bitwidth for unsigned)
- `SignedFloat`/`UnsignedFloat`: Exactly one must be `true`
- `FiniteFloat`/`ExtendedFloat`: Exactly one must be `true`

**Returns:** Concrete AIFloat instance with pre-computed value and encoding sequences.

**Examples:**
```julia
# 8-bit signed finite format with 4-bit precision
sf = AIFloat(8, 4; SignedFloat=true, FiniteFloat=true)

# 6-bit unsigned extended format with 3-bit precision  
ue = AIFloat(6, 3; UnsignedFloat=true, ExtendedFloat=true)

# Construct from abstract type
uf = AIFloat(AkoUnsignedFinite{8, 4})
```

## Accessor Functions

### `floats`

```julia
floats(x::AbstractAIFloat) -> Vector{<:AbstractFloat}
```

Return the vector of floating-point values in the format.

### `codes`

```julia
codes(x::AbstractAIFloat) -> Vector{<:Unsigned}
```

Return the vector of encoding values (bit patterns) for the format.

## Type Introspection

### Bitfield Size Functions

```julia
nBits(T::Type{<:AbstractAIFloat}) -> Int

nSignBits(T::Type{<:AbstractAIFloat}) -> Int
nExpBits(T::Type{<:AbstractAIFloat}) -> Int
nSigBits(T::Type{<:AbstractAIFloat}) -> Int  
nFracBits(T::Type{<:AbstractAIFloat}) -> Int
```

Query the size of a bitfield of a format.

- `nBits`: Total bitwidth
- `nSigBits`: Significand bits (including implicit leading bit)
- `nFracBits`: Fractional bits (trailing significand bits nSigBits - 1)
- `nSignBits`: Sign bits (1 for signed, 0 for unsigned)
- `nExpBits`: Exponent bits


### Special Value Counts

```julia
nZeros(T::Type{<:AbstractAIFloat}) -> Int       # Always 1
nNaNs(T::Type{<:AbstractAIFloat}) -> Int        # Always 1

nInfs(T::Type{<:AbstractAIFloat}) -> Int        # 0 for finite, 1-2 for extended
nPosInfs(T::Type{<:AbstractAIFloat}) -> Int     # 1 for extended, 0 for finite
nNegInfs(T::Type{<:AbstractAIFloat}) -> Int     # 1 for signed extended, 0 otherwise
```

### Complete Magnitude and Value Counts

```julia
nMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nNonzeroMagnitudes(T::Type{<:AbstractAIFloat}) -> Int

nValues(T::Type{<:AbstractAIFloat}) -> Int
nNumericValues(T::Type{<:AbstractAIFloat}) -> Int
nNonzeroNumericValues(T::Type{<:AbstractAIFloat}) -> Int
```

Count different categories of representable values.

### Subset Magnitude and Value Counts

```julia
nPrenormalMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nSubnormalMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nNormalMagnitudes(T::Type{<:AbstractAIFloat}) -> Int

nPrenormalValues(T::Type{<:AbstractAIFloat}) -> Int
nSubnormalValues(T::Type{<:AbstractAIFloat}) -> Int
nNormalValues(T::Type{<:AbstractAIFloat}) -> Int
```

## Type Predicates

### Format Type Predicates

```julia
is_aifloat(T::Type) -> Bool

is_signed(T::Type{<:AbstractAIFloat}) -> Bool
is_unsigned(T::Type{<:AbstractAIFloat}) -> Bool

is_finite(T::Type{<:AbstractAIFloat}) -> Bool
is_extended(T::Type{<:AbstractAIFloat}) -> Bool
```

