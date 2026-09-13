---
rg: 2
id: fp-type-fp-group-is-type-f-iff-wall-class-vanishes
kind: claim
title: "A finitely presented group of type FP is of type F iff its Wall class in reduced K_0(ZG) vanishes"
distinct_from:
  g-times-z-type-f-iff-finitely-dominated-classifying-space: that packages this criterion together with the G x Z and finite-domination equivalences; this isolates the criterion for finitely presented groups of type FP (F iff FL iff sigma(G) = 0), with no product factor, so it can be consumed by the reduced-K_0 firewall and the product criterion
---

Let `G` be finitely presented and of type FP, and let `P_* → Z` be a finite
resolution by finitely generated projective `ZG`-modules. Define the Wall class

    σ(G) = Σ_i (−1)^i [P_i]  ∈  K̃_0(ZG) = K_0(ZG) / Z·[ZG].

It does not depend on the resolution. The following are equivalent:

1. `G` is of type F;
2. `G` is of type FL;
3. `σ(G) = 0`.

Up to sign, `σ(G)` is Wall's finiteness obstruction of any finitely dominated
`K(G,1)`.

Model test. For `G = Z^n` the Koszul resolution is free, so `σ(G) = 0`, and `G`
is of type F. The hypotheses exclude groups with torsion, so the familiar
nonzero classes of `K̃_0(ZQ)` for finite `Q` never occur as `σ(G)`.
