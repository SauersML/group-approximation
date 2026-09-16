---
rg: 2
id: thompson-v-ah-subgroups-lack-z2-via-bleak-salazar-diaz
kind: route
title: A Z^2 in an acylindrically hyperbolic group is elliptic, hence a free factor with a loxodromic, giving Z^2 * Z inside V
target: thompson-v-acylindrically-hyperbolic-subgroups-lack-z2
requires:
  - ah-elliptic-torsion-free-subgroup-is-free-factor
  - z2-free-z-does-not-embed-in-thompson-v
artifacts:
  - research/artifacts/thompson-t-disjoint-pair-witness-obstructions-2026-09-16.md
---

## Imported from Osin

D. Osin, *Acylindrically hyperbolic groups*, arXiv:1304.1246v4 (16 Apr 2015; title and
dates from the arXiv abstract page, fetched 2026-09-16). The v4 PDF was fetched on
2026-09-16 and its text was extracted locally. Quotations restore symbols lost in
extraction. The journal version was not compared.

- **Theorem 1.1.** "Let G be a group acting acylindrically on a hyperbolic space. Then G
  satisfies exactly one of the following three conditions. (a) G has bounded orbits.
  (b) G is virtually cyclic and contains a loxodromic element. (c) G contains infinitely
  many independent loxodromic elements."
- **Definition 1.3.** "We call a group G acylindrically hyperbolic if it satisfies either of
  the equivalent conditions (AH1)–(AH4)", among them "(AH2) G admits a non-elementary
  acylindrical action on a hyperbolic space".
- **After Theorem 1.1.** "If the action is acylindrical, non-elementarity is equivalent to
  condition (c) from Theorem 1.1."
- **Corollary 6.9.** "Suppose that a group G acts acylindrically on a hyperbolic space S.
  Then there exists N ∈ N such that for every loxodromic element g ∈ G, the centralizer
  C_G(g) contains a cyclic subgroup of index at most N."

Osin's hyperbolic spaces are geodesic ("S is δ-hyperbolic if it is geodesic and for any
geodesic triangle ..."), which matches the setting of
`ah-elliptic-torsion-free-subgroup-is-free-factor`.

## Proof

Let `H ≤ V` be acylindrically hyperbolic. By (AH2), `H` acts non-elementarily and
acylindrically on a hyperbolic space `S`. By the remark after Theorem 1.1, `H` contains
independent loxodromic elements. Suppose `P ≤ H` with `P ≅ Z^2`.

1. The restriction of the action to `P` is acylindrical, directly from the definition,
   since the defining bound counts fewer elements.
2. Apply Theorem 1.1 to `P`. Case (b) fails, since `Z^2` is not virtually cyclic.
3. Case (c) fails. Otherwise `P` contains a loxodromic `x`, and `P ≤ C_H(x)` because `P` is
   abelian. By Corollary 6.9 for the action of `H`, `C_H(x)` is virtually cyclic, and so is
   `P`, which is false.
4. So `P` has bounded orbits. It is nontrivial and torsion-free, so by
   `ah-elliptic-torsion-free-subgroup-is-free-factor` some loxodromic `h ∈ H` has
   `⟨P, h⟩ = P * ⟨h⟩ ≅ Z^2 ∗ Z`.
5. So `Z^2 ∗ Z ≤ H ≤ V`, contradicting `z2-free-z-does-not-embed-in-thompson-v`. ∎

Replacing `V` by any group `G` without a subgroup `Z^2 ∗ Z` gives the general statement.

**Consequences, with their inputs.**
- *`T` and `V` are not acylindrically hyperbolic.* Both contain `Z^2`, for example two
  elements of `F` supported in disjoint dyadic intervals.
- *No acylindrically hyperbolic subgroup of `T` contains a disjoint pair.* Let
  `a, b ∈ T \ {1}` have disjoint supports on `S^1`. They commute, since each is the identity
  on the other's support and preserves its own. Each has a fixed point (the other's
  support is fixed pointwise), and an orientation-preserving homeomorphism of an interval
  of finite order is the identity, so both have infinite order. If `a^m b^n = 1`, then
  `a^m = b^(−n)` is supported in `supp(a) ∩ supp(b) = ∅`, so `m = n = 0`. Hence
  `⟨a, b⟩ ≅ Z^2`. Finally `T ≤ V` (stated in the introduction of arXiv:0911.0979v1:
  "T ≤ V"). The artifact, §1, writes this out.
