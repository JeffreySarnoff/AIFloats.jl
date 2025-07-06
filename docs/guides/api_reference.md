# AIFloats.jl API Reference

## Constructor Functions

### `AIFloat`

```julia
AIFloat(bitwidth::Int, sigbits::Int; SignedFloat::Bool, UnsignedFloat::Bool, 
        FiniteFloat::Bool, ExtendedFloat::Bool) -> AbstractAIFloat

AIFloat(T::Type{<:AbstractAIFloat}) -> AbstractAIFloat
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
uf = AIFloat(AbstractUnsignedFinite{8, 4})
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

### Bit Allocation Functions

```julia
nBits(T::Type{<:AbstractAIFloat}) -> Int
nSigBits(T::Type{<:AbstractAIFloat}) -> Int  
nFracBits(T::Type{<:AbstractAIFloat}) -> Int
nSignBits(T::Type{<:AbstractAIFloat}) -> Int
nExpBits(T::Type{<:AbstractAIFloat}) -> Int
```

Query the bit allocation of a format.

- `nBits`: Total bitwidth
- `nSigBits`: Significand bits (including implicit leading bit)
- `nFracBits`: Fractional bits (nSigBits - 1)
- `nSignBits`: Sign bits (1 for signed, 0 for unsigned)
- `nExpBits`: Exponent bits

### Value Count Functions

```julia
nValues(T::Type{<:AbstractAIFloat}) -> Int
nNumericValues(T::Type{<:AbstractAIFloat}) -> Int
nNonzeroNumericValues(T::Type{<:AbstractAIFloat}) -> Int
nMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nNonzeroMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
```

Count different categories of representable values.

### Special Value Counts

```julia
nNaNs(T::Type{<:AbstractAIFloat}) -> Int        # Always 1
nZeros(T::Type{<:AbstractAIFloat}) -> Int       # Always 1
nInfs(T::Type{<:AbstractAIFloat}) -> Int        # 0 for finite, 1-2 for extended
nPosInfs(T::Type{<:AbstractAIFloat}) -> Int
nNegInfs(T::Type{<:AbstractAIFloat}) -> Int
```

### Subnormal Counts

```julia
nPrenormalMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nSubnormalMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nPrenormalValues(T::Type{<:AbstractAIFloat}) -> Int
nSubnormalValues(T::Type{<:AbstractAIFloat}) -> Int
nNormalMagnitudes(T::Type{<:AbstractAIFloat}) -> Int
nNormalValues(T::Type{<:AbstractAIFloat}) -> Int
```

## Type Predicates

### Format Type Predicates

```julia
is_aifloat(T::Type) -> Bool
is_signed(T::Type{<:AbstractAIFloat}) -> Bool
is_unsigned(T::Type{<:AbstractAIFloat}) -> Bool
is_finite(T::Type{<:AbstractAIFloat}) -> Bool
is_extended(T::Type{