using Tables, CSV

pbf = precision(BigFloat)
setprecision(BigFloat, 64)

full_file_path16 = s"C:\JuliaCon\P3109\base16\unsigned\finite\bits15\binary15uf.base16.csv"
full_file_path10 = s"C:\JuliaCon\P3109\base10\unsigned\finite\bits12\binary12uf.base10.csv"

ctable16 = CSV.read(full_file_path16, columntable; typemap=IdDict(Float64 => String));
ctable_clean16 = map(v->map(x->strip(x),v), ctable16);

tiny16 = ctable_clean16[2][2];
huge16 = ctable_clean16[2][end-1];

ctable10 = CSV.read(full_file_path10, columntable; typemap=IdDict(Float64 => String));
ctable_clean10 = map(v->map(x->strip(x),v), ctable10);

tiny10 = ctable_clean10[2][2];
huge10 = ctable_clean10[2][end-1];

const log102 = log10(2)
const log210 = log2(10)

function findexp(str::AbstractString, chr::Char)
    idx = findfirst(==(chr), str)
    isnothing(idx) && return idx
    Meta.parse(str[idx+1:end])
end

function absexp(str::AbstractString)
    aexp = absexp(str, 'e')
    if isnothing(aexp)
        aexp = absexp(str, 'p')
        if isnothing(aexp)
            aexp = 0
        end
    end
    aexp
end

function absexp(str::AbstractString, chr::Char)
    expval = findexp(str, chr)
    isnothing(expval) && return expval
    aexpval = abs(expval)
    if chr === 'e'
        aexpval
    elseif chr === 'p'
        ceil(Int, aexpval * log102)
    else
        error("char $chr not recognized")
    end
end

typefromexp(exp::Int) = (abs(exp) < 300) ? Float64 : BigFloat

typefromexp(x::AbstractString) = typefromexp(absexp(x))

parsestr(x) = Base.parse(typefromexp(x), x)