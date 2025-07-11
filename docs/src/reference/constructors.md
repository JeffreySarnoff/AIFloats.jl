# Constructor Reference

## Primary Constructor

```@docs
AIFloat
```

The main entry point for creating AIFloat format instances. Supports both parametric specification and abstract type-based construction.

### Parameter-Based Construction

```julia
AIFloat(bitwidth::Int, precision::Int, signedness::Symbol, domain::Symbol)
```

**Parameters:**
- `bitwidth`: Total number of bits (3 ≤ bitwidth ≤ 15)
- `precision`: Significand bits including implicit bit (1 ≤ precision ≤ bitwidth)
- `signedness`: Either `:signed` or `:unsigned`
- `domain`: Either `:finite` or `:extended`

**Examples:**
```julia
# 4-bit signed 