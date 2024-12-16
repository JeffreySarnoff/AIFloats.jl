# FloatsForML.jl
### The constructive model for P3109 compliant MicroFloats.
##### Copyright 2024-2025 by Jeffrey A. Sarnoff

[![Aqua QA](https://raw.githubusercontent.com/JuliaTesting/Aqua.jl/master/badge.svg)](https://github.com/JuliaTesting/Aqua.jl)  [![JET](https://img.shields.io/badge/%F0%9F%9B%A9%EF%B8%8F_tested_with-JET.jl-233f9a)](https://github.com/aviatesk/JET.jl)

----

FloatsForML.jl 

#### The parameters are available

A `BaseFloat` contains two fields, `encoding` and `values`.
- `encoding` holds the sequence of value encodings for the specified Bitwidth and Precision
- `values` holds the sequence floating-point values  for the specified Bitwidth and Precision

#### The fields are available
- MF32encoding = encoding(MF32)
- MF32values = values(MF32)

### Technical Notes

#### BaseFloats are used to construct other MicroFloat types
- they are not intended for direct use
  - see UnsignedMicroFloats.jl
  - see SignedMicroFloats.jl

#### The values of a BaseFloat are finite non-negative numbers:
- there is one 0
- there are no negative values
- there are no NaNs
- there are no Infs

#### Types used
```
if the Bitwidth is <= 8
    the encoding is a vector of UInt8
    the values are a vector of Float32
else
    the encoding is a vector of UInt16
    the values are a vector of Float64
```
