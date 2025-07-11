# Glossary

## A

**AbstractAIFloat**
: The root abstract type for all AI floating-point formats, parameterized by bitwidth, significand bits, and signedness.

**Augmented Binary Rationals**
: The mathematical foundation of AIFloats: finite binary rationals extended with NaN for undefined operations, denoted $\mathbb{B}^\diamond = (\mathbb{Q}_2^* \cup \{\text{NaN}\})$.

## B

**Bias (Exponent)**
: The constant subtracted from the raw exponent field to produce signed exponent values. Calculated as $2^{(\text{exp\_bits} - 1)} - \text{is\_signed}$.

**Bit Budget**
: The allocation of available bits among sign, exponent, and significand fields, subject to format-specific constraints.

**Bitwidth**
: The total number of bits in a floating-point representation, ranging from 3 to 15 bits in AIFloats.

## C

**Code**
: The integer encoding corresponding to a floating-point value, stored as UInt8 or UInt16 depending on bitwidth.

**Code-Value Correspondence**
: The bijective mapping between integer encodings and floating-point values maintained by each AIFloat format.

## D

**Domain (Extended/Finite)**
: The value domain classification:
- **Finite**: Real numbers ∪ {NaN}
- **Extended**: Real numbers ∪ {NaN, ±∞} or {NaN, +∞}

**Dynamic Range**
: The ratio between the largest and smallest representable magnitudes in a format.

## E

**Encoding Sequence**
: The ordered sequence of integer codes [0x00, 0x01, ..., 0xFF] corresponding to a format's value sequence.

**Exception-Free Arithmetic**
: The design principle ensuring no computational exceptions (NaN generation, infinity overflow) occur during normal operations.

**Exponent Field**
: The bit field encoding the power-of-two scaling factor, with width determined by remaining bits after significand allocation.

**Extended Binary Rationals**
: Binary rational numbers augmented with infinities: $\mathbb{Q}_2^* = \mathbb{Q}_2 \cup \{\pm\infty\}$.

## F

**Format Family**
: The four-way classification of AIFloat types:
- SignedFinite, SignedExtended, UnsignedFinite, UnsignedExtended

**Fractional Bits**
: The explicit significand bits excluding the implicit leading bit, equal to precision - 1.

## I

**IEEE P3109**
: The draft IEEE standard for arithmetic formats for machine learning, providing formal specifications for reduced-precision arithmetic.

**Implicit Bit**
: The leading significand bit (0 for subnormals, 1 for normals) that is not explicitly stored but assumed based on exponent value.

**Index**
: Julia's 1-based array position corresponding to a code's location in the value sequence.

## M

**Magnitude Foundation**
: The base sequence of non-negative values before sign extension, generated through significand-exponent scaling.

**Mixed Precision**
: The use of different AIFloat formats for different components within a single computation.

## N

**Normal Values**
: Floating-point values with implicit leading bit 1, following the pattern $(1 + \text{fraction}) \times 2^{\text{unbiased\_exponent}}$.

## P

**Prenormal Region**
: The value domain containing zero plus all subnormal magnitudes, totaling $2^{(\text{precision} - 1)}$ values.

**Precision**
: The total number of significand bits including the implicit leading bit, determining the granularity of representable values.

## Q

**Quantization**
: The process of mapping continuous or higher-precision values to the discrete set of AIFloat-representable values.

## S

**Significand**
: The fractional part of a floating-point representation, consisting of an implicit bit plus fractional bits.

**Signedness**
: The format property determining whether negative values are representable (:signed) or only non-negative values (:unsigned).

**Stochastic Rounding**
: A probabilistic rounding mode where the selection between adjacent representable values depends on the input's relative distance.

**Subnormal Values**
: Floating-point values with implicit leading bit 0, providing gradual underflow near zero with pattern $\text{fraction} \times 2^{\text{exp\_min}}$.

## T

**Table Lookup**
: The computational approach using precomputed arrays for ultra-fast evaluation of unary and binary functions on small formats.

**Type-Level Computation**
: The technique of performing calculations at compile time using Julia's type system, eliminating runtime overhead.

## U

**ULP (Unit in Last Place)**
: The spacing between consecutive representable values, varying by magnitude due to exponential scaling.

**Unbiased Exponent**
: The true exponent value after bias subtraction, ranging symmetrically around zero.

## V

**Value Sequence**
: The ordered array of floating-point values corresponding to sequential integer encodings, forming the format's canonical representation.

## Z

**Zero Encoding**
: The canonical representation of zero, always encoded as 0b0...0 across all AIFloat formats.