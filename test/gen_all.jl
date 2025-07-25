
using AIFloats, ArbNumerics, Quadmath
using AIFloats: clean_frexp

kmin = 2
kmax = 15

ufs = [AIFloat(k, p, :unsigned, :finite)    for k in kmin:kmax for p in  1:k];
ues = [AIFloat(k, p, :unsigned, :extended)  for k in kmin:kmax for p in  1:k];
sfs = [AIFloat(k, p, :signed, :finite)      for k in kmin:kmax for p in  1:k-1];
ses = [AIFloat(k, p, :signed, :extended)    for k in kmin:kmax for p in  1:k-1];

ufcodes = map(codes, ufs);
uecodes = map(codes, ues);
sfcodes = map(codes, sfs);
secodes = map(codes, ses);

ufvals = map(floats, ufs);
uevals = map(floats, ues);
sfvals = map(floats, sfs);
sevals = map(floats, ses);

for vals in (ufvals, uevals, sfvals, sevals)
  for idx in 1:length(vals)
    for idx2 in 1:length(vals[idx])
        str = string(vals[idx][idx2])
        if str === "nan" || endswith(str, "inf")
            if str == "nan"
                vals[idx][idx2] = NaN
            elseif str == "+inf"  || str == "inf"  
                vals[idx][idx2] = Inf
            else # str == "-inf"
                vals[idx][idx2] = -Inf
            end
        end
    end
  end
end

frexp_ufvals = map(clean_frexp, ufvals);
frexp_uevals = map(clean_frexp, uevals);
frexp_sfvals = map(clean_frexp, sfvals);
frexp_sevals = map(clean_frexp, sevals);

clean_ufvals = map(safe_ldexp, frexp_ufvals);
clean_uevals = map(safe_ldexp, frexp_uevals);
clean_sfvals = map(safe_ldexp, frexp_sfvals);
clean_sevals = map(safe_ldexp, frexp_sevals);


#   narrow the type 

function isnarrowed(::Type{T}, xs::Vector{F}) where {T,F}
    if T == F
        return true
    elseif  sizeof(T) > sizeof(F)
        return false
    end

    ys = map(x->convert(T, x), xs)
    zs = map(x->convert(F, x), ys)
    all( map((x,y) -> issame(x,y),xs, ys) )
end

@inline function issame(x, y)
    (isnan(x) && isnan(y)) || (x == y)
end

ufvals_narrow  = copy(ufvals);
uevals_narrow  = copy(uevals);
sfvals_narrow  = copy(sfvals);
sevals_narrow  = copy(sevals);

narrows32  = map(v->isnarrowed(Float32,v), ufvals); 
narrows64  = map(v->isnarrowed(Float64,v), ufvals);
narrows128 = map(v->isnarrowed(Float128,v), ufvals);
narrowsBig = ufvals[ (!).(narrows32 .| narrows64 .| narrows128) ];
anyBig = !isempty(narrowsBig) && sum(narrowsBig) > 0

ufvals_narrow[narrows32] .= 
    map(v->map(Float32,v), ufvals[narrows32]);
ufvals_narrow[narrows64] .= 
    map(v->map(Float64,v), ufvals[narrows64]);
ufvals_narrow[narrows128] .= 
    map(v->map(Float128,v), ufvals[narrows128]);
if anyBig
    ufvals_narrow[narrowwsBig] .=
    map(v->map(BigFloat,v), ufvals[narrowsBig]);
end

narrows32  = map(v->isnarrowed(Float32,v), uevals); 
narrows64  = map(v->isnarrowed(Float64,v), uevals);
narrows128 = map(v->isnarrowed(Float128,v), uevals);
narrowsBig = uevals[ (!).(narrows32 .| narrows64 .| narrows128) ];
anyBig = !isempty(narrowsBig) && sum(narrowsBig) > 0

uevals_narrow[narrows32] .= 
    map(v->map(Float32,v), uevals[narrows32]);
uevals_narrow[narrows64] .= 
    map(v->map(Float64,v), uevals[narrows64]);
uevals_narrow[narrows128] .= 
    map(v->map(Float128,v), uevals[narrows128]);

# "[+/- inf]" as BigFloat

if anyBig
    uevals_narrow[narrowwsBig] .=
    map(v->map(BigFloat,v), uevals[narrowsBig]);
end

narrows32  = map(v->isnarrowed(Float32,v), sfvals); 
narrows64  = map(v->isnarrowed(Float64,v), sfvals);
narrows128 = map(v->isnarrowed(Float128,v), sfvals);
narrowsBig = sfvals[ (!).(narrows32 .| narrows64 .| narrows128) ];
anyBig = !isempty(narrowsBig) && sum(narrowsBig) > 0

sfvals_narrow[narrows32] .= 
    map(v->map(Float32,v), sfvals[narrows32]);
sfvals_narrow[narrows64] .= 
    map(v->map(Float64,v), sfvals[narrows64]);
sfvals_narrow[narrows128] .= 
    map(v->map(Float128,v), sfvals[narrows128]);
if anyBig
    sfvals_narrow[narrowwsBig] .=
    map(v->map(BigFloat,v), sfvals[narrowsBig]);
end

narrows32  = map(v->isnarrowed(Float32,v), sevals); 
narrows64  = map(v->isnarrowed(Float64,v), sevals);
narrows128 = map(v->isnarrowed(Float128,v), sevals);
narrowsBig = sevals[ (!).(narrows32 .| narrows64 .| narrows128) ];
anyBig = !isempty(narrowsBig) && sum(narrowsBig) > 0

sevals_narrow[narrows32] .= 
    map(v->map(Float32,v), sevals[narrows32]);
sevals_narrow[narrows64] .= 
    map(v->map(Float64,v), sevals[narrows64]);
sevals_narrow[narrows128] .= 
    map(v->map(Float128,v), sevals[narrows128]);

    #  cannot parse "[+/- inf]" as BigFloat
if anyBig
    sevals_narrow[narrowwsBig] .=
    map(v->map(BigFloat,v), sevals[narrowsBig]);
end

function astype(::Type{T}, xs::Vector{F}) where {T,F}
    ys = filter(!isnan,xs)
    zs = map(x->convert(T, x), ys)
    all( iszero.( ys .- zs))
end

all([astype(Float64, floats(AIFloat(12,p,:signed,:finite))) for p in 1:11])
