---
rg: 2
id: fpbs-residual-class-has-torsion-products-proof
kind: route
title: Project amenable subgroups to the factors, then apply Khezeli and Osin
target: fpbs-residual-class-has-torsion-products
requires:
  - fpbs-khezeli-products-have-fixed-price-one
  - fpbs-osin-ah-groups-not-products-not-torsion
  - fpbs-monster-groups-have-only-finite-amenable-subgroups
---

Complete proof.

1. **Finitely generated.** The union of generating sets of `H x {1}` and
   `{1} x K` generates `G`.
2. **No infinite amenable subgroup.** Let `S <= G` be amenable. Its projections
   `π_H(S) <= H` and `π_K(S) <= K` are quotients of `S`, so they are amenable,
   hence finite. So `S <= π_H(S) x π_K(S)` is finite.
3. **Nonamenable.** `G` is infinite, so by 2 it is not amenable.
4. **Hypothesis 3 of the residual claim.** By 2 there is no infinite amenable
   subgroup at all, so the hypothesis holds vacuously.
5. **Fixed price one.** `fpbs-khezeli-products-have-fixed-price-one`, since
   `H` and `K` are infinite and countable.
6. **Not acylindrically hyperbolic.** By
   `fpbs-osin-ah-groups-not-products-not-torsion` item 1, an acylindrically
   hyperbolic `G = H x K` would have a finite factor.

**Examples.** `fpbs-monster-groups-have-only-finite-amenable-subgroups` says
that torsion Tarski monsters and `B(m,n)` (`m >= 2`, odd `n >= 1003`) are
infinite and finitely generated, with only finite amenable subgroups. Products
of torsion groups are torsion, so every example is in part (R0) of the hull
claim.
