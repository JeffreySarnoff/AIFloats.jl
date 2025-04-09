
For each member of this family of floating-point formats, this package provides the encoding and paired value sequence. There are two sorts of ML floats, Signed and Unsigned. There are two kinds of each, Finite and Extended. All have one NaN value and one Zero value. Extended kinds have a [signed] infinity, while Finite kinds do not.

 - Signed
   - Finite
   - Extended
 - Unsigned
   - Finite
   - Extended
  
| Sort | Kind | 1 NaN | 1 Zero | Infinity | Family      | Generalized Name |
|------|------|-------|--------|----------|-------------|:----------------:|
| Signed   | Finite   | yes | yes | N/A   | SFinite     | s𝚏Binary\<bitwidth\>p\<precision\>      |
| Signed   | Extended | yes | yes | ±Inf  | SExtended   | seBinary\<bitwidth\>p\<precision\>      |
| Unsigned | Finite   | yes | yes | N/A   | UFinite     | u𝚏Binary\<bitwidth\>p\<precision\>      |
| Unsigned | Extended | yes | yes | +Inf  | UExtended   | ueBinary\<bitwidth\>p\<precision\>      |

The bitwidths of the members of each family may be as low as 2 and as large as 15. The admissible precisions range from 1 through bitwidth-1.  

All value sequences have subnormals *except for precisions of 1*.
