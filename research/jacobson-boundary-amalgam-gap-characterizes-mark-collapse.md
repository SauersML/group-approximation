---
rg: 2
id: jacobson-boundary-amalgam-gap-characterizes-mark-collapse
kind: claim
title: The boundary-amalgam matrix infimum exactly detects collapse of the literal Jacobson head mark
distinct_from:
  jacobson-two-braid-gap-characterizes-mark-collapse: that concerns the weaker presentation with a refuted positive infimum; this concerns two exact finite factors containing the additional shifted and boundary relations, with TS and first-braid words left mixed.
artifacts:
  - research/artifacts/jacobson-boundary-amalgam-gap-equivalence-2026-09-08.md
---

Let `Xi=<F *_(P_Q x K_P) J | (hb)^3=1,W=1>` have the specified
finite factors and words from
`jacobson-mixed-cells-reconstruct-full-first-level-root-packet`.
The mark `w_Q=x_13,Q` is nontrivial in this finitely presented group.

Let `gamma_Xi` be the infimum of

```text
max(||(rho_J(h) rho_F(b))^3-I||, ||W-I||)
```

over all positive matrix dimensions and exact representations of `F,J`
on that dimension agreeing on `P_Q x K_P`, with `rho_F(w_Q)!=I`.
The domain is nonempty, and `0<=gamma_Xi<=2`. Strict positivity is
equivalent to every norm-matrix-corona homomorphism from `Xi` killing
`w_Q`. In particular, strict positivity would imply that `Xi` is non-MF.

Zero infimum is equivalent to existence of a corona homomorphism
retaining this mark; it is not asserted equivalent to MF of `Xi`.
No sign of the infimum is settled by this equivalence.

DERIVATION
jacobson-boundary-amalgam-relative-lifting-proof
