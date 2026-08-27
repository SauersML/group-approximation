---
rg: 2
id: branch-flip-pauli-cancellation-proof
kind: route
title: Cross the two child characters by their sign-flip automorphism
target: branch-flip-pauli-extraction-cancels-schur-surplus
requires:
  - schur-child-center-sign-flip-is-group-automorphism
  - oriented-schur-child-branching-identity
  - symmetrized-reset-collapses-schur-flow-to-one-ray
---

The defining relation `eta q_* eta^(-1)=Jq_*` gives
`[eta,q_*]=J`.  Neither `q_*` nor `eta` belongs to the central selector
subgroup modulo `J`: `q_*` has a nonzero child-generator coordinate and
`eta` has a nonzero semidirect-factor coordinate.  Normal form in
`C_f semidirect <eta>` proves `(BFC1)`.

On `J=-1`, the two corrected child-center characters are exchanged by
`eta`.  In the ordered basis of their two isotypic lines, the corrected child
sign is `diag(1,-1)` and `eta` is the swap matrix.  They generate `M_2`, so
the restriction `T|C_f=C_+ directSum C_-` becomes one irreducible module for
the crossed product.  This is precisely the inverse of the restriction step
which produced the factor two.  Summing over the balanced selector sectors
recovers the one-ray calculation `(SRC6)--(SRC7)`.

