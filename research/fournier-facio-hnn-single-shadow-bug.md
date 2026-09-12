---
rg: 2
id: fournier-facio-hnn-single-shadow-bug
kind: claim
title: The pre-quotient Fournier--Facio HNN skeleton contains one nontrivial shadow-bug commutator
distinct_from:
  fournier-facio-torsion-free-skeleton: that claim tracks the whole simple subgroup inside a compression defect of the published common quotient; this claim stops before that quotient and extracts only one commutator word in the shadow residual.
  defect-saturation-full-mf-radical: that claim is the final routed full-radical output; this is its weaker one-word analytic seed.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
  - GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean
---

In the double HNN extension

```text
E=<P,u_1,u_2 | u_i P u_i^-1=P_i>,
```

choose `s,x` in the simple factor `S<=P` with `[s,x]!=1`, put
`c=u_1^-1 s u_1`, and let `w=[s,x]`.  Britton injectivity gives `w!=1` in
`E`.  The relations give `[c,P]=1` and `u_1 c u_1^-1=s`; one-sided Kazhdan
transport therefore kills `[s,x]` in the normalized-HS shadow of every
operator-norm almost representation:

```text
1 != w in S(E).
```

The group `E` is finitely presented, torsion-free, and acylindrically
hyperbolic.  Lean extracts the word from `FournierFacioDefectData` as
`exists_nontrivial_opToHSShadowBug`.
