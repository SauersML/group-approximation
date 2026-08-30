---
rg: 2
id: bcv-halt-completeness-has-computable-readable-factor-bound
kind: claim
title: BCV HALT completeness has a computable readable-factor bound independent of halting time
distinct_from:
  bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs: that proves each individual HALT strategy has some finite readable orbit after its halting time is known; this asks for one total computable bound from the machine description alone.
  bounded-readable-factor-zirs-value-has-computable-upper-hierarchy: that proves effective compactness once an integer atom bound is supplied; this asks the BCV completeness construction to supply that bound uniformly.
  perfect-gap-zpc-has-finite-readable-translate-algebra: that directly asks for a specially chosen NONHALT gap witness with some finite factor; this is a HALT-side uniformity premise from which such a witness would follow by a restricted diagonalization.
---

There is a total computable function `B` on encodings of Turing machines
such that, whenever `M` halts, the Bowen--Chapman--Vidick tailored game
`G_M` has a perfect ZPC strategy whose full readable translate algebra
satisfies

```text
dim D_infinity <= B(M).                                  (BHB1)
```

The value `B(M)` must be computable before running `M` and must be
independent of the actual halting time `N`.  A bound `B(M,N)` obtained
from the finite signed-permutation strategy after observing that `M` halts
does not satisfy this claim and is not sufficient for the diagonal argument.

## Current boundary

BCV perfect completeness produces a finite signed-permutation strategy for
each halting machine, so every such strategy has a finite readable factor.
The published recursive proof bounds its size through the recursively built
strategy and hence through the halting time.  It does not state `(BHB1)`.

Question Reduction does not visibly reset this complexity.  In its honest
completeness strategy on

```text
C^(F_2^k) tensor H,
```

the readable `SamZ` atoms give the first tensor factor, while the readable
answer projections contain block corners of the source readable projections.
Pauli-X translations move those corners between blocks.  Thus source
readable-factor complexity is retained, rather than erased, at this stage.
A proof of `(BHB1)` would have to find a later uniform collapse in Answer
Reduction or Parallel Repetition, or construct a different perfect
completeness strategy with a computably bounded readable factor.  No such
collapse is presently established.
