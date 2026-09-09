"""Exact executable reference for the P3109/D1 Maude specification."""
module P3109Reference

export BinaryFormat, Projection, finite, decode, encode, project, SpecAPI
public FiniteValue,
    SpecialValue,
    NAN,
    POS_INF,
    NEG_INF,
    Residual,
    Decision,
    SIGNED,
    UNSIGNED,
    FINITE,
    EXTENDED,
    RoundMode,
    Saturation,
    RoundPolicy,
    BlockProjection,
    BlockValue,
    valid_format,
    valid_code,
    is_datum,
    bitwidth,
    precision_bits,
    exponent_bias,
    format_name,
    scalar,
    block_apply,
    scaled,
    mathematical_equal,
    mathematical_less,
    Symbolic,
    Contracts,
    BoundFormat,
    ExternalFormat,
    BINARY16,
    BINARY32,
    BINARY64,
    BFLOAT16,
    UNKNOWN,
    NEAREST_EVEN,
    NEAREST_AWAY,
    UP,
    DOWN,
    TO_ZERO,
    TO_ODD,
    STOCHASTIC_A,
    STOCHASTIC_B,
    STOCHASTIC_C,
    SAT_NONE,
    SAT_FINITE,
    SAT_PROPAGATE

include("values.jl")
include("formats.jl")
include("policies.jl")
include("codec.jl")
include("projection.jl")
include("arithmetic.jl")
include("symbolic.jl")
include("generated_kernels.jl")
include("operations.jl")
include("conformance.jl")
include("contracts.jl")
include("spec_api.jl")

end
