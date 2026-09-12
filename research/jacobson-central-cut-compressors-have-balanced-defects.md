---
rg: 2
id: jacobson-central-cut-compressors-have-balanced-defects
kind: claim
title: Central and finitary projection cuts have explicitly matched compressed-shift defects
artifacts:
  - research/artifacts/jacobson-central-cut-compressors-have-balanced-defects-2026-09-08.md
---

Let `A,B` be commuting representations of a finite group, let
`P(g)=A(g)B(g)`, and suppose `T P(g) T*=B(g)`. For a central
projection `e` in the group algebra of any subgroup, set `C=e(B)`
and `D=e(P)`. Then `C,D` commute, `TDT*=C`, and

```text
S=CTC=TDC,
S*S=CD,             SS*=TCDT*,
C-S*S=C(1-D),       C-SS*=TD(1-C)T*.
```

The two defect projections have equal rank. For the invariant cut,
the second defect is exactly the nontrivial contragredient-pair
invariant channel, so it cannot be discarded by treating invariant
projections as additive under tensor products.

Even on the full exact admissible `B,C,T` domain with a surviving
head, conjugation by `T` need not preserve `Alg(p_B,p_P)`. The
permutation `(x,y,z) |-> (y^(-1)z,x,y)` on regular `G^3`,
amplified to the regular large packet and glued along the full overlap,
gives `T p_B T*=p_Q`, outside that two-projection algebra. This
example imposes no smallness on the four remaining word errors.

For an arbitrary projection `p in C[L]`, the finitary group algebra,
the polar partial isometry of `ptp` has an explicit unitary extension
in the `p` corner. A finite-coordinate permutation conjugates `p`
to `t*pt` inside a finite group algebra, where blockwise cancellation
matches both defects. This conclusion holds in every representation,
including for noncentral finitary cuts. It excludes neither the tail
packet's nonfinitary coefficients nor arbitrary multiplicity-space cuts.

The artifact also constructs reduced finite-dimensional covariance
models with `p_B=0` and nontrivial `A`, using rational stationary
weights in the finite representation ring. These models are not
asserted to satisfy the full coherent group presentation. Neither
statement decides its matrix gap.

DERIVATION
jacobson-commuting-projection-and-fusion-balance-proof
