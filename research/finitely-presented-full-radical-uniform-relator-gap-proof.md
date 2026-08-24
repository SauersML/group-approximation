---
rg: 2
id: finitely-presented-full-radical-uniform-relator-gap-proof
kind: route
title: Diagonalize approximate relator solutions into one corona representation
target: finitely-presented-full-radical-uniform-relator-gap
requires:
  - hilbert-hotel-block-cover-is-unconditional
---

Assume first that `Rad_MF(G)=G` and `(R1)` fails.  For one `epsilon>0`,
choose matrix tuples `U^(n)` whose relator defects tend to zero while one
generator stays at distance at least `epsilon` from the identity.  Their
classes in the norm matrix corona satisfy every defining relator exactly,
so the presentation gives a homomorphism `G` into the corona.  It is
nontrivial on that generator, contradicting total radical.

Conversely, let `rho:G->U(Q)` be a corona homomorphism and lift the images of
the finite generating set to coordinate unitaries.  Every defining relator
has coordinate defect tending to zero.  Applying `(R1)` for each positive
`epsilon` makes every generator converge to the identity.  Hence `rho` is
trivial and `Rad_MF(G)=G`.

Positivity of `gap_G(epsilon)` is exactly the quantified statement `(R1)`.
The finitely presented Hilbert-hotel cover has total MF radical, so the
criterion applies to its fixed finite presentation.
