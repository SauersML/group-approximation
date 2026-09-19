---
rg: 2
id: relative-hull-quotient-with-full-mf-radical
kind: claim
title: Every finitely presented torsion-free acylindrically hyperbolic group has a full-MF-radical quotient injective on a prescribed finite set
distinct_from:
  common-quotient-onto-normal-subgroup: that is the small-cancellation input, a common quotient of two acylindrically hyperbolic groups onto a prescribed normal subgroup, with no MF content; this feeds it the saturated group and reads off the MF conclusion.
  defect-saturation-full-mf-radical: that produces one group with full MF radical; this produces, for every finitely presented torsion-free acylindrically hyperbolic source and every finite subset of it, a quotient with the same package that is injective there.
  two-generated-single-element-hull-router: that fills a two-generated acylindrical common quotient from one nontrivial element and is a step inside the saturation construction; this consumes the finished saturated group and controls a prescribed finite subset of an arbitrary source.
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `G` be finitely presented, torsion-free, and acylindrically hyperbolic,
and let `Omega subset G` be finite.  Then there is a surjection

```text
phi : G ->> P
```

with `phi|_Omega` injective, such that `P` is two-generated, finitely
presented, torsion-free, acylindrically hyperbolic, has property (T), and
satisfies `Res_MF(P)=P`.

Taking `G=F_2` and `Omega` the ball of radius `n` gives such groups whose
Cayley graph in the inherited two-generator marking has girth greater than
`n`.
