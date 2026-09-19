---
rg: 2
id: atlas-a4-three-word-amplified-gap
kind: claim
title: Two A4 pair-cubes and collision 19243 have a uniform amplified Hilbert-Schmidt gap
distinct_from:
  atlas-a4-three-moment-classical-separator: that is the exact convex-hull inequality for classical automorphism alignments; this claim asks for its genuinely matrix-valued amplification to arbitrary relative chart unitaries.
  atlas-a4-holonomy-coherence-gap: that first exactifies the full thirty-context graph and asks for an S3 covariance ceiling; this claim attacks three fixed kernel words directly, before any context-network compiler.
artifacts:
  - experiments/atlas_triangle_19243_two_context_gap.py
  - experiments/atlas-word-19243.json
---

REFUTED by [[atlas-three-word-gap-permutation-countermodel]]: an exact
12-point permutation model at multiplicity 2 in the C6--S3 core meets
every hypothesis and violates the gap.  The statement below is kept as
the record of what was asked for, not as an open target.

Let `rho_k=Reg(A8) tensor I_k` on `C^(20160 k)`.  Represent factor one by
`rho_k` and factor two by

```text
x |-> U rho_k(x) U^*
```

for an arbitrary unitary `U`.  Let `u,v` be packet tree indices `6910,6940`
from `atlas-a4-two-context-collision-gap`, and let `q=q_19243`.

Prove that there is one constant `epsilon>0`, independent of `k`, such that
for every `k>=1` and every `U`,

```text
||u(U)-1||_2^2
 + ||v(U)-1||_2^2
 + ||q(U)-1||_2^2
 >= epsilon.                                            (A4-3W-GAP)
```

Normalized Hilbert--Schmidt norm is used throughout.

This is now a **three-word noncommutative CSP**.  The classical restriction of
`U` to an inner/outer chart normalizer has the sharp lower bound `epsilon=2`
by `atlas-a4-three-moment-classical-separator`, but the theorem only asks for
some positive amplified constant.  No rounding to one alignment, no thirty-way
synchronization, and no quantitative S3 covariance estimate is part of the
statement.

## Attempts

- **Noncommutative SOS / SDP.**  Write
  `E(U)=sum_(x in {u,v,q})(2-x(U)-x(U)^*)`.  It is a fixed matrix-valued
  Laurent polynomial in one unitary variable over the finite coefficient
  algebra `C[A8]`.  Search for a cyclic sum-of-squares certificate
  `tau(E)>=epsilon` in the universal tracial free product
  `M_20160 * C(T)`.  Any rational certificate is automatically stable under
  multiplicity amplification.
- **Exploit the tiny S3 support.**  The two selected pair-cubes and collision
  use a very small same-chart subgroup inside `A8`.  Compress the regular
  representation to its finite isotypic decomposition for that subgroup
  before optimizing over `U`; external multiplicity should then be the only
  growing coordinate.
- **Moment relaxation instead of operator rounding.**  Only words of bounded
  degree in `U,U^*` occur.  Build the finite tracial moment matrix through that
  degree, impose the exact regular coefficient moments, and ask whether its
  SDP dual separates zero energy.  This attacks the desired scalar inequality
  directly rather than reconstructing a chart alignment.
- **Failure is informative.**  A sequence with energy tending to zero would be
  an explicit three-relation matrix-valued countermodel to the classical PCP.
  Its low-degree moment limits should reveal exactly which nonclassical sector
  evades the two-context hitting set, giving a smaller replacement gadget.
