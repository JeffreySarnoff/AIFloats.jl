using Tables, CSV

pbf = precision(BigFloat)
setprecision(BigFloat, 64)

full_file_path16 = s"C:\JuliaCon\P3109\base16\unsigned\finite\bits15\binary15uf.base16.csv"
full_file_path10 = s"C:\JuliaCon\P3109\base10\signed\extended\bits11\binary11se.base10.csv"

ctable16 = CSV.read(full_file_path16, columntable; typemap=IdDict(Float64 => String));
ctable_clean16 = map(v->map(x->strip(x),v), ctable16);

tiny16 = ctable_clean16[2][2];
huge16 = ctable_clean16[2][end-1];

ctable10 = CSV.read(full_file_path10, columntable; typemap=IdDict(Float64 => String));
ctable_clean10 = map(v->map(x->strip(x),v), ctable10);

tiny10 = ctable_clean10[2][2];
huge10 = ctable_clean10[2][end-1];

const log10of2 = log10(2);
const log2of10 = log2(10);

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
        ceil(Int, aexpval * log10of2)
    else
        error("char $chr not recognized")
    end
end

typefromexp(exp::Int) = (abs(exp) < 300) ? Float64 : BigFloat

typefromexp(x::AbstractString) = typefromexp(absexp(x))

parsestr(x) = Base.parse(typefromexp(x), x)

full_file_path16_5 = s"C:\JuliaCon\P3109\base16\signed\extended\bits5\binary5se.base16.csv" ;
full_file_path16_6 = s"C:\JuliaCon\P3109\base16\signed\extended\bits6\binary6se.base16.csv" ;
full_file_path16_8 = s"C:\JuliaCon\P3109\base16\signed\extended\bits8\binary8se.base16.csv" ;
full_file_path16_10 = s"C:\JuliaCon\P3109\base16\signed\extended\bits10\binary10se.base16.csv";

ctable16_6 = CSV.read(full_file_path16_6, columntable; typemap=IdDict(Float64 => String));
ctable16_6_clean = map(v->map(x->strip(x),v), ctable16_6);
ctable16_6_codes = parse.(UInt8, ctable16_6_clean[1]);
ctable16_6_floats = [map(x->parse(Float64,x), ctable16_6_clean[i]) for i=2:length(ctable16_6_clean)];

ctable16_8 = CSV.read(full_file_path16_8, columntable; typemap=IdDict(Float64 => String));
ctable16_8_clean = map(v->map(x->strip(x),v), ctable16_8);
ctable16_8_codes = parse.(UInt8, ctable16_8_clean[1]);
ctable16_8_floats = [map(x->parse(Float64,x), ctable16_8_clean[i]) for i=2:length(ctable16_8_clean)];

ctable16_10 = CSV.read(full_file_path16_10, columntable; typemap=IdDict(Float64 => String));
ctable16_10_clean = map(v->map(x->strip(x),v), ctable16_10);
ctable16_10_codes = parse.(UInt16, ctable16_10_clean[1]);
ctable16_10_floats = [map(x->parse(Float64,x), ctable16_10_clean[i]) for i=2:length(ctable16_10_clean)];

