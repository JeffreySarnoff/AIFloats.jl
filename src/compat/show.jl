# display of datums — a view, never a semantic
#
# Four styles, selected process-wide by set_show_style! or per-stream by an
# IOContext property. No style may change a result: the style is consumed by
# show and by nothing else. And show must never be the thing that throws — a
# failing testset has to be able to print the values it compares.

const SHOW_STYLE_KEY = :binary_show_style
const DEFAULT_SHOW_STYLE = Ref{Symbol}(:value)

"""
    VALID_SHOW_STYLES

The four datum display styles: `:value` (the default — a datum prints as the
number it denotes), `:codepoint`, `:datum` (`(value ⇆ code)`), and `:typed`
(`formatname(value ⇆ code)`).
"""
const VALID_SHOW_STYLES = (:value, :codepoint, :datum, :typed)

"""
    set_show_style!(style::Symbol)

Set the process-wide datum display style — one of [`VALID_SHOW_STYLES`](@ref).
Per-stream override: `IOContext(io, :binary_show_style => style)`.

# Examples

```jldoctest
julia> set_show_style!(:value)
:value
```
"""
function set_show_style!(style::Symbol)
    style in VALID_SHOW_STYLES ||
        throw(ArgumentError("show style must be one of $(VALID_SHOW_STYLES), got :$style"))
    DEFAULT_SHOW_STYLE[] = style
end

"""
    get_show_style()
    get_show_style(io::IO)

The active datum display style: the stream's `:binary_show_style` property if
set, else the process-wide default.
"""
get_show_style() = DEFAULT_SHOW_STYLE[]
get_show_style(io::IO) = get(io, SHOW_STYLE_KEY, DEFAULT_SHOW_STYLE[])::Symbol

function _show_datum_pair(io::IO, x::BinaryValue)
    print(io, "(")
    isnan(x) ? print(io, "NaN") : show(io, decode(x))
    print(io, " ⇆ 0x")
    print(io, string(codepoint(x); base = 16, pad = 2 * sizeof(CodeType(x))))
    print(io, ")")
end

function _show_binaryvalue(io::IO, x::BinaryValue)
    style = get_show_style(io)
    if style === :value
        isnan(x) ? print(io, "NaN") : show(io, decode(x))
    elseif style === :codepoint
        show(io, codepoint(x))
    elseif style === :datum
        _show_datum_pair(io, x)
    else # :typed
        print(io, formatname(BinaryFormatOf(x)))
        _show_datum_pair(io, x)
    end
    nothing
end

# ONE dispatcher behind BOTH show methods — a duplicate 2-arg show that
# bypasses the dispatcher is the recorded historical bug.
Base.show(io::IO, x::BinaryValue) = _show_binaryvalue(io, x)
Base.show(io::IO, ::MIME"text/plain", x::BinaryValue) = _show_binaryvalue(io, x)

# the datum TYPE prints as its format alias name — but only when fully
# instantiated. Julia hands partially-applied forms (TypeVar parameters) to
# show while printing method signatures; those fall back to Base. (The same
# hazard, and the same fix, as Binary's own show methods.)
function _bv_format(T::Type{<:BinaryValue})
    D = Base.unwrap_unionall(T)
    D isa DataType && length(D.parameters) == 2 || return nothing
    F = D.parameters[1]
    F isa DataType && F <: Binary || return nothing
    any(p -> p isa TypeVar, Base.unwrap_unionall(F).parameters) && return nothing
    F
end

function Base.show(io::IO, T::Type{<:BinaryValue})
    F = _bv_format(T)
    F === nothing && return invoke(show, Tuple{IO, Type}, io, T)
    print(io, formatname(F))
    nothing
end