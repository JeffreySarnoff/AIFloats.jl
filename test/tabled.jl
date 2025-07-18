using AIFloats
using Tables, CSV, Printf, PrettyTables, JLD2

function astype(::Type{T}, xs::Vector{F}) where {T,F}
    ys = filter(!isnan,xs)
    zs = map(x->convert(T, x), ys)
    all( iszero.( ys .- zs))
end

codes1x15 = [[]]; # retrieve by index from 2 on
append!(codes1x15, [codes(AIFloat(K, 1, :signed, :finite)) for K=2:15]);

uf1x15 = [[]];
append!(uf1x15, [[floats(AIFloat(K, P, :unsigned, :finite)) for P=1:K] for K=2:15]);

ue1x15 = [[]];
append!(ue1x15, [[floats(AIFloat(K, P, :unsigned, :extended)) for P=1:K] for K=2:15]);

sf1x15 = [[]];
append!(sf1x15, [[floats(AIFloat(K, P, :signed, :finite)) for P=1:K-1] for K=2:15]);

se1x15 = [[]];
append!(se1x15, [[floats(AIFloat(K, P, :signed, :extended)) for P=1:K-1] for K=2:15]);

#=

julia> map(length, se1x15)'
1×15 adjoint(::Vector{Int64}) with eltype Int64:
 0  1  2  3  4  5  6  7  8  9  10  11  12  13  14

julia> map(length, uf1x15)'
1×15 adjoint(::Vector{Int64}) with eltype Int64:
 0  2  3  4  5  6  7  8  9  10  11  12  13  14  15

=#
#=

julia> all(map(xs->astype(Float64, xs),uf1x15[10]))
true

julia> all(map(xs->astype(Float64, xs),uf1x15[11]))
true

julia> all(map(xs->astype(Float64, xs),uf1x15[12]))
false

[(map(xs->astype(Float128, xs),uf1x15[i])) for i=2:15]
(true, true, true, true, true, true, true, 
 true, true, true, true, true, true, true)

Float32s  with uf1x15[ 2: 8]
Float64s  with uf1x15[ 9:11]
Float128s with uf1x15[12:15]

Float32s  with sf1x15[ 2: 9]
Float64s  with sf1x15[10:12]
Float128s with sf1x15[13:15]
=#



sf1x15_128 = map(x->map(y->Float128.(y),x), sf1x15);
sf1x12_64  = map(x->map(y->Float64.(y),x), sf1x15[1:12]);
sf1x9_32  = map(x->map(y->Float32.(y),x),sf1x15[1:9]);

se1x15_128 = map(x->map(y->Float128.(y),x), se1x15);
se1x12_64  = map(x->map(y->Float64.(y),x),  se1x15[1:12]);
se1x9_32  = map(x->map(y->Float32.(y),x), se1x15[1:9]);

uf1x15_128 = map(x->map(y->Float128.(y),x), uf1x15);
uf1x1x11_64  = map(x->map(y->Float64.(y),x), uf1x15[1:11]);
uf1x8_32  = map(x->map(y->Float32.(y),x), uf1x15[1:8]);

ue1x1x15_128 = map(x->map(y->Float128.(y),x), ue1x15);
ue1x11_64  = map(x->map(y->Float64.(y),x),  ue1x15[1:11]);
ue1x8_32  = map(x->map(y->Float32.(y),x), ue1x15[1:8]);

codes_15 = codes1x15;

sf13x15_128 = map(x->map(y->Float128.(y),x), sf1x15[13:15]);
sf10x12_64  = map(x->map(y->Float64.(y),x), sf1x15[10:12]);
sf1x9_32  = map(x->map(y->Float32.(y),x),sf1x15[1:9]);
sf_15 = (sf1x9_32..., sf10x12_64..., sf13x15_128...);

se13x15_128 = map(x->map(y->Float128.(y),x), se1x15[13:15]);
se10x12_64  = map(x->map(y->Float64.(y),x),  se1x15[10:12]);
se1x9_32  = map(x->map(y->Float32.(y),x), se1x15[1:9]);
se_15 = (se1x9_32..., se10x12_64..., se13x15_128...);

uf12x15_128 = map(x->map(y->Float128.(y),x), uf1x15[12:15]);
uf9x11_64  = map(x->map(y->Float64.(y),x), uf1x15[9:11]);
uf1x8_32  = map(x->map(y->Float32.(y),x), uf1x15[1:8]);
uf_15 = (uf1x8_32..., uf9x11_64..., uf12x15_128...);

ue12x15_128 = map(x->map(y->Float128.(y),x), ue1x15[12:15]);
ue9x11_64  = map(x->map(y->Float64.(y),x), ue1x15[9:11]);
ue1x8_32  = map(x->map(y->Float32.(y),x), ue1x15[1:8]);
ue_15 = (ue1x8_32..., ue9x11_64..., ue12x15_128...);

using Tables, CSV, Printf, PrettyTables, JLD2, Latexify

holdprecision = precision(BigFloat)
setprecision(BigFloat, 64)

sf_13to15_BigFloat = map(x->map(y->BigFloat.(y),x), sf1x15)[13:15];
sf_13to15_Float128 = map(x->map(y->Float128.(y),x), sf1x15)[13:15];
sf_1to12_Float64   = map(x->map(y->Float64.(y),x),  sf1x15[1:12]);
sf_1to12_hexstr = map(v->map(v1->map(x->@sprintf("%a",x), v1),v), sf_1to12_Float64);

se_13to15_BigFloat = map(x->map(y->BigFloat.(y),x), se1x15)[13:15];
se_13to15_Float128 = map(x->map(y->Float128.(y),x), se1x15)[13:15];
se_1to12_Float64   = map(x->map(y->Float64.(y),x),  se1x15[1:12]);
se_1to12_hexstr = map(v->map(v1->map(x->@sprintf("%a",x), v1),v), se_1to12_Float64);

uf_12to15_BigFloat = map(x->map(y->BigFloat.(y),x), uf1x15)[12:15];
uf_12to15_Float128 = map(x->map(y->Float128.(y),x), uf1x15[12:15]);
uf_1to11_Float64   = map(x->map(y->Float64.(y),x),  uf1x15[1:11]);
uf_1to11_hexstr = map(v->map(v1->map(x->@sprintf("%a",x), v1),v), uf_1to11_Float64);

ue_12to15_BigFloat = map(x->map(y->BigFloat.(y),x), ue1x15)[12:15];
ue_12to15_Float128 = map(x->map(y->Float128.(y),x), ue1x15[12:15]);
ue_1to11_Float64   = map(x->map(y->Float64.(y),x),  ue1x15[1:11]);
ue_1to11_hexstr = map(v->map(v1->map(x->@sprintf("%a",x), v1),v), ue_1to11_Float64);


setprecision(BigFloat, holdprecision)
