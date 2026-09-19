---
rg: 2
id: nonhyperlinear-bloop-central-sign-corner-route
kind: route
title: Feed the fixed loop BCS through the authenticated augmentation corner
target: nonhyperlinear-property-t-free-explicit-mf-witness
requires:
  - lin-explicit-fixed-bcs-gap-via-generic-conversion
  - nonhyperlinear-bloop-central-sign-corner
  - nonhyperlinear-normal-augmentation-corner-kills-mf
artifacts:
  - research/artifacts/nonhyperlinear-normal-augmentation-source-audit-2026-08-30.md
---

The fixed BCS `B_loop` has a tracial state and no CE tracial state.  The
corner gate supplies a countable group `G`, the nontrivial finite normal
subgroup `K=<J>`, and the unital map

```text
A(B_loop) -> q_K C[G]q_K,       q_K=(1-J)/2.
```

These are exactly the hypotheses of
`nonhyperlinear-normal-augmentation-corner-kills-mf`.  Its stronger conclusion
is `K<=Rad_MF(G)`, so the named involution `J` is killed by every
norm-matrix-corona homomorphism.  No Property `(T)` input occurs in this
route.  This proves the first explicit-group endpoint of
`property-t-free-manuscript-results`; the combined manuscript root still has
the independent Leavitt and torsion-free obligations recorded there.
