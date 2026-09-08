Why are External-format and mathematical-real contracts being added as separate, uninstantiated interfaces.  What would it take for mathematical-real contracts to be added as instantiated interfaces?

They are separate because the plan explicitly requires that boundary: executable rational arithmetic, symbolic real expressions, and mathematical contracts have different guarantees. An uninstantiated contract states what a backend must satisfy without implying that we already have one.
For external formats, the permitted draft delegates encoding details to other standards. Implementing those codecs would require an authorized source for those details.
For mathematical reals, an instantiated interface would need:
1. A concrete Maude backend representing real values and implementing the contract’s operations.
2. A Maude view mapping the contract’s sorts and operations to that backend.
3. Evidence that the backend satisfies the contract’s axioms. Maude accepting the view’s syntax does not establish this.
4. A parameterized consumer module instantiated with that view, connecting the backend to arithmetic and projection.
The substantive difficulty is item 3. Rationals cannot represent sqrt(2). Algebraic numbers cover exact roots but exclude values such as π and exp(1). Symbolic expressions with certified interval evaluation cover more useful cases, but some equality, domain, and rounding-boundary questions must remain unresolved.
A practical next stage would therefore be an instantiated certified-real evaluation interface: expressions provide meaning, and checked certificates justify particular comparisons or projections. Its contract would explicitly allow unresolved results. That would be useful and executable, while the stronger contract for all mathematical reals would remain a separate obligation.
I’m preserving that distinction in this implementation, as the plan specifies. Instantiating the current full-real contract with the rational or symbolic module without those proofs would overstate what the specification establishes.
