---
rg: 2
id: g-times-z-type-f-iff-g-f-infinity-with-finite-cd
kind: claim
title: "G x Z is of type F iff G is of type F_infinity with finite cd iff G is finitely presented of type FP"
---

For every group `G` the following are equivalent:

1. `G × Z` is of type F;
2. `G` is of type `F_∞` and `cd_Z G < ∞`;
3. `G` is finitely presented and of type FP.

This is the equivalence stated in Zaremsky's Problem 1.21
(`zaremsky-1-21-g-times-z-type-f-implies-g-type-f`). The route
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof` gives the argument:
`G` is a retract of `G × Z`, which gives (1) ⇒ (3); a product resolution whose
Euler class vanishes identically gives (3) ⇒ (1). The backward direction is the
algebraic form of Mather's trick (a finitely dominated `X` has `X × S^1`
homotopy equivalent to a finite complex).

Model test. `G = Z^n`: all three hold. `G` = a Bestvina–Brady group of type FP
that is not finitely presented: (3) fails, and (1) fails too, since `G × Z` is
not finitely presented.
