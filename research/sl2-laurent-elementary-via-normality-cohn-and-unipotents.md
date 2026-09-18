---
rg: 2
id: sl2-laurent-elementary-via-normality-cohn-and-unipotents
kind: route
title: "Normality of E_2, elementary non-unimodular Cohn matrices, and unipotent generation give SL_2(Z[t,t^-1]) = E_2"
target: sl2-laurent-integers-equals-elementary-subgroup
requires:
  - sl2-laurent-elementary-iff-three-unipotent-conditions
  - sl2-laurent-elementary-subgroup-is-normal
  - laurent-nonunimodular-cohn-matrices-are-elementary
  - sl2-polynomial-integers-lie-in-laurent-unipotent-subgroup
---

This route is not `sl2-laurent-integers-fg-via-elementary-generation`: that route
takes `G = E_2` as an input for finite generation, while this one proves `G = E_2`
itself.

By item 1 of `sl2-laurent-elementary-iff-three-unipotent-conditions`, the three inputs
together give `SL_2(Z[t,t^{-1}]) = E_2(Z[t,t^{-1}])`:

- (N) `sl2-laurent-elementary-subgroup-is-normal`;
- (C) `laurent-nonunimodular-cohn-matrices-are-elementary`;
- (U) `sl2-polynomial-integers-lie-in-laurent-unipotent-subgroup`.

The same item shows that each input is also necessary. So a disproof of any one of
them refutes the target, and this route loses nothing.

The inputs call for different tools:

- (N) and (C) are statements about single explicit matrices `C(p,q)`, open to search
  and to degree or width invariants;
- (U) is a statement about the quotient `SL_2(Z[t]) / (U_2(R) ∩ SL_2(Z[t]))`, open to
  tree and Fricke methods (`sl2-laurent-unipotent-quotient-is-polynomial-quotient`,
  `polynomial-unipotent-subgroup-fricke-compatible`).
