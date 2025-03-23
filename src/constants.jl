const BitsMin = 2
const BitsMaxSmall = 8
const BitsMinLarge = 9
const BitsMax = 15

const IsUnsigned = false
const IsSigned   = true

const IsFinite   = false
const IsExtended = true

typeforcode(Bits::Integer) = 
    ifelse(Bits <= BitsMaxSmall, UInt8, UInt16)

typeforfloat(Bits::Integer) =
    ifelse(Bits <= BitsMaxSmall, Float32, Float64)