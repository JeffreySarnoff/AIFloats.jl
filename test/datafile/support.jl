using Pkg
cd(s"C:\JuliaCon\floatenv"); using Pkg; Pkg.activate(pwd()); Pkg.add(path="C:\\github\\FloatsForML.jl")
using Printf, Arrow, CSV, Tables, Dictionaries, FloatsForML

const PathSep = Sys.iswindows() ? "\\" : "/"

pfxs = (:uf, :ue, :se, :sf)
prefixes = NamedTuple{pfxs}( ("uf", "ue", "se","sf") )

# parentdir = abspath(joinpath("C:/","data/P3109_KPdata/share"))
parentdir = abspath(s"C:/data/P3109_KPdata/share/Binary2-10/")
basedir = joinpath(parentdir, "Binary2-10_UnsdSgnd_FiniteExtd")

dirSigned = joinpath(basedir, "signed")
dirUnsigned = joinpath(basedir, "unsigned")

dirSextended = joinpath(dirSigned, "extended")
dirSfinite = joinpath(dirSigned, "finite")
dirUextended = joinpath(dirUnsigned, "extended")
dirUfinite = joinpath(dirUnsigned, "finite")

binarysubdirs = pushfirst!([string("Binary",i) for i in 2:10], "")

dirsUF = map(fil->joinpath(dirUfinite, fil), binarysubdirs)
dirsUE = map(fil->joinpath(dirUextended, fil), binarysubdirs)
dirsSE = map(fil->joinpath(dirSextended, fil), binarysubdirs)
dirsSF = map(fil->joinpath(dirSfinite, fil), binarysubdirs)

alldirs = NamedTuple{pfxs}( (dirsUF, dirsUE, dirsSE, dirsSF) )


bitsrange = 2:length(alldirs.uf)

t = [(k .=> collect(p for p in 1:k-1)) for k in 2:10]
m = map.(x -> (first(x), last(x)), t)

exts = ["csv", "arrow"]
ext = exts[1]
results = []

for pfx in values(prefixes)
    filebasenames=pushfirst!(collect(map(kp -> string(pfx,"BinaryK",kp[1],"P",kp[2],".",ext), m[i]) for i in 1:length(m)), [""])
    push!(results, filebasenames)
end

filenames = NamedTuple{pfxs}(results)

filepaths_uf = [[""]]
filepaths_ue = [[""]]
filepaths_sf = [[""]]
filepaths_se = [[""]]

for idx in bitsrange
    push!(filepaths_uf, map(str->joinpath(alldirs.uf[idx], str),  filenames.uf[idx]))
    push!(filepaths_ue, map(str->joinpath(alldirs.ue[idx], str),  filenames.ue[idx]))
    push!(filepaths_sf, map(str->joinpath(alldirs.sf[idx], str),  filenames.sf[idx]))
    push!(filepaths_se, map(str->joinpath(alldirs.se[idx], str),  filenames.se[idx]))
end

#=

table = Arrow.Table(filepath)
codes = eltype(table.codes).(table.codes)
floats = eltype(table.floats).(table.floats)

file_name_ext = split(filepath, PathSep)[end]
file_name, file_ext = split(file_name_ext, ".")

=#

function file_name_ext(filepath)
     name_ext = split(filepath, PathSep)[end]
     file_name, file_ext = split(name_ext, ".")
     return file_name, file_ext
end

function arrowtable(filepath)
    if !isfile(filepath)
        throw(ErrorException("$(filepath) not found"))
    end
    Arrow.Table(filepath)
end

function arrowcols(filepath)
    table = arrowtable(filepath)
    codes = eltype(table.codes).(table.codes)
    floats = eltype(table.floats).(table.floats)
    return (; codes, floats)
end

function arrowcolumntable(filepath)
    table = arrowtable(filepath)
    Tables.columntable(table)
end

function savetocsv(filepath, table)
    filedir = dirname(filepath)
    mkpath(filedir)
    CSV.write(filepath, table; delim=',', header=["codes", "floats"])
end

filepath = "C:\\data\\P3109_KPdata\\share\\Binary2-10\\Binary2-10_UnsdSgnd_FiniteExtd\\unsigned\\finite\\Binary5\\ufBinaryK5P2.arrow"

coltable = arrowcolumntable(filepath)
fdir = abspath(joinpath("C:/","data","FloatsForML"))
fpath = joinpath(fdir, "table.csv")
savetocsv(fpath, coltable)

#

ilog2(i::T) where {T<:Integer} = i > 0 ? 8*sizeof(T) - leading_zeros(i) - 1 : throw(DomainError("$i must be > 0"))
ilog2p1(i::T) where {T<:Integer} = iszero(i) ? 0 : ilog2(i) + 1

function hexstr(x::UInt8)
    nbits = ilog2p1(x)
    if nbits == 0
        return "0x00"
    elseif nbits <= 4
        @sprintf("0x0%x", x)
    else
        @sprintf("0x%2x", x)
    end
end

function hexstr(x::UInt16)
    nbits = ilog2p1(x)
    if nbits == 0
        return "0x0000"
    elseif nbits <= 4
        @sprintf("0x000%1x", x)
    elseif nbits <= 8
        @sprintf("0x00%2x", x)
    elseif nbits <= 12
        @sprintf("0x0%3x", x)
    else
        @sprintf("0x%4x", x)
    end
end

function floatstr(x::AbstractFloat)
    @sprintf("%a", x)
end

function scistr(x::Float32)
    @sprintf("%e", x)
end

function prints(x::AbstractFloat)
    str = @sprintf("%64.64e",x)
    a,e = split(str, "e")
    b = rstrip(a,'0')
    string(b, "e", e)
  end
