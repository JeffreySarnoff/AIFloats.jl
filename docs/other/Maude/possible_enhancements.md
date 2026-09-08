# Instantiating the contracts

The mathematical-real and external-format contracts state obligations separately
from the executable rational core and symbolic expressions. Neither currently
has an implementation view.

An instantiated interface needs:

1. A backend representing values and implementing the contract's operations.
2. A Maude view mapping the contract's sorts and operations to that backend.
3. Evidence that the backend satisfies the contract's axioms; accepting the
   view's syntax does not establish this.
4. A parameterized consumer instantiated with the view, connecting the backend
   to arithmetic and projection.

External codecs also need encoding definitions from the standards to which the
draft delegates them. Rationals cannot implement the full real contract because
they exclude values such as sqrt(2); algebraic numbers also exclude π and exp(1).

A practical extension is symbolic expressions with certified enclosure evaluation.
Checked certificates could justify selected comparisons and projections while
unresolved equality, domain, or rounding-boundary questions remain residual.
This needs its own partial-evaluation contract and soundness proof. The stronger
contract for all mathematical reals would remain a separate obligation.
