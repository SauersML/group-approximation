---
rg: 2
id: single-shadow-word-saturation-compiler
kind: claim
title: One nontrivial shadow word compiles into a 2-generated full-MF-radical group
root: true
distinct_from:
  hyperlinear-to-mf-saturation-compiler: that is the subgroup-valued analytic backend assuming a routing map; this theorem starts with one word in a finitely generated recursively presented group and constructs the finite-presentation and acylindrical routing environment.
  acylindrical-hyperlinear-saturation-compiler: that theorem requires the source itself to be finitely presented, torsion-free, acylindrically hyperbolic, and Kazhdan; this theorem uses Higman and a free-product envelope and demands none of those source properties.
  threshold-free-reverse-kleene-mf-higman: that metatheorem assumes direct MF-radical membership in NONHALT; this theorem accepts the strictly weaker operator-to-HS shadow membership of one already nontrivial word.
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

Let `G` be finitely generated and recursively presented.  If

```text
1 != w in S(G)=R_{infinity->2}(G),
```

then there exists a nontrivial 2-generated finitely presented
acylindrically hyperbolic property-(T) group `Q` with

```text
normMFResidual Q = top.
```

Every homomorphism from `Q` to an operator-MF group is trivial and every
nontrivial quotient again has full MF residual.  If the source is already
finitely presented, torsion-free, and acylindrically hyperbolic, the Higman
and free-product passes are omitted and `Q` may be chosen torsion-free.
