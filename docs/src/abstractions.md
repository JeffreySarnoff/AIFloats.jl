# Abstractions

```mermaid
graph TD
    A[AbstractMLFloat] 
    --> B[AbsSignedMLFloat]
    --> C[AbsUnsignedMLFloat]
```

export AbstractMLFloat,
         AbsSignedMLFloat,
           AbsSignedExtendedMLFloat, AbsSignedFiniteMLFloat,
              SExtendedMLFloats,        SFiniteMLFloats,
         AbsUnsignedMLFloat,
           AbsUnsignedExtendedMLFloat, AbsUnsignedFiniteMLFloat,
              UExtendedMLFloats,          UFiniteMLFloats,
       #
