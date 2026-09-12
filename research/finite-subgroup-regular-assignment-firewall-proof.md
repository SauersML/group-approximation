---
rg: 2
id: finite-subgroup-regular-assignment-firewall-proof
kind: route
title: Assign every finite-subgroup element its regular rank and check invariance, consistency and independence
target: finite-subgroup-data-cannot-force-defect-submultiplicativity
requires:
  - unitriangular-data-cannot-assemble-corner-leavitt-families
artifacts:
  - research/artifacts/cylinder-commutant-independence-and-weyl-firewall-2026-09-12.md
---

Artifact Section 3, Lemma 3.1 and Theorem 3.2.

1. **Consistency.** `F_2[K']` is free over `F_2[K]` for `K <= K'`, so `dim(alpha F_2[K])/|K|` does not
   depend on the finite group containing the support.
2. **Rank models.** On a countable locally finite subgroup, regular representations along an exhausting
   chain assemble, through an ultraproduct, into a rank model with these ranks. For an infinite subgroup
   the fixed space of `K_n` has normalized dimension `1/|K_n|`, so there is no fixed vector.
3. **Invariance.** Conjugation by any unit is an algebra isomorphism between finite-subgroup algebras.
4. **Values.** `x = iota_A(x_12(1))` and `y = iota_A(x_23(1))` generate a dihedral group of order `8`.
   The kernel of left multiplication by `(1+y)(1+x)` on `F_2[D_8]` has dimension
   `4 + dim((1+x)F_2[D_8] cap (1+y)F_2[D_8]) = 5`, so `rk_reg(D_A) = 3/8`. Disjoint cylinder groups commute
   and meet trivially, so ranks multiply by the tensor decomposition of the regular module.
5. **Scope.** Weyl elements over `F_2`, halving sheets, prefix doubling, the swap, and conjugation by torus
   units or compressors only produce finite-subgroup relations or rank equalities between conjugates
   (artifact 3.3), and all of those hold for `rk_reg`.
