---
rg: 2
id: corona-coefficient-module-decoder
kind: claim
title: Decode compatible finite root multiplicities into one finite projective corona module
---

OPEN.  Let `R` be a countable ring with a binary Leavitt family and let
`rho:E_n(R)->U(Q_d)` be a norm-corona representation in which a specified
root `rho(x_ij(r_0))` survives.

Construct a nonzero finitely generated projective `Q_d`-module `P_rho` and a
unital ring homomorphism

```text
R -> End_(Q_d)(P_rho).
```

The finite additive and Heisenberg multiplicity germs already provide exact
finite restrictions of the desired action.  The missing content is a
finite-projective compactness theorem assembling the compatible restrictions
on one common nonzero module.

## Attempts

- **Take the inverse limit of rank germs.**  Compatible scalar ranks do not
  determine compatible projection representatives or coefficient
  intertwiners.  The resulting inverse-limit object can be countably
  generated while the cancellation theorem requires one nonzero finitely
  generated projective corona module.
- **Diagonalize coordinate exactifications.**  Each finite window can be
  exactified on a tail, but the conjugating corrections depend on the window.
  Their selected projections can move through the matrix coordinates and
  have zero common rank germ despite compatible restriction multiplicities.
- **Deferred live attack.**  Prove a compact-containment/tightness theorem in
  the projection monoid of the norm corona: a surviving root must support one
  nonzero rank-bounded subprojection invariant under all four fixed Leavitt
  coefficient germs.  No such alignment follows from `K_0` data alone.

## Attempts

- **Use only the additive Fourier projections.**  This cannot recover the
  Leavitt arrows: one additive character can remain nontrivial on every
  prefix idempotent, so binary prefix projections do not split the active
  mass into two equivalent copies.
- **Exactify each finite Heisenberg window separately.**  This recovers each
  finite multiplication table, but the correcting unitaries and isotypic
  corners may depend on the window.  Branching compatibility of rank germs
  does not by itself produce nested coordinate projections in one fixed
  matrix amplification.
- **Take an inverse limit of multiplicity vectors.**  The inverse limit gives
  a coherent type measure, not a finitely generated projective `Q_d`-module.
  It does not control a uniform stabilization size or provide bounded
  operators realizing the four Leavitt coefficients on a common carrier.
- **Compress to the active spectral projection of the surviving root.**  The
  projection is nonzero, but general coefficient roots move it.  Repeated
  compression introduces boundary terms, and no operator-norm estimate is
  presently known that makes the two inverse relations exact in the corona.

The unresolved statement is a bounded-stabilization gluing theorem:
compatible finite Heisenberg multiplicities with a surviving root must admit
one nonzero projective carrier and one coherent coefficient-ring action.
