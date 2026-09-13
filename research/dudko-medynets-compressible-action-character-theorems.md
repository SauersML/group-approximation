---
rg: 2
id: dudko-medynets-compressible-action-character-theorems
kind: claim
title: Dudko--Medynets compressible-action character theorems, including the non-simple extension theorem and the dyadic compressibility lemma
distinct_from:
  no-proper-character-groups-avoid-amenable-orbit-full-groups: that imports only the simple-group theorem (their Theorem 2.9) and consumes it for orbit full groups; this imports the definition of compressible actions, both character theorems and the dyadic interval lemma, which the Lodha--Moore character classification needs.
  thompson-f-character-simplex: that imports the Higman--Thompson corollary at F_(2,1); this imports the general theorems behind it so they can be applied to other groups.
---

**ESTABLISHED by citation.**  From A. Dudko and K. Medynets, *Finite factor
representations of Higman--Thompson groups*, Groups Geom. Dyn. 8 (2014) 375--389,
arXiv:1212.1230.

1. **Compressible actions.**  An action of `G` on an infinite regular Hausdorff
   space `X` is *compressible* if some base `U` of the topology satisfies:
   - (i) every `supp(g)` lies in some member of `U`;
   - (ii) for all `U_1, U_2` in `U` some `g` has `g(U_1) ⊆ U_2`;
   - (iii) for all `U_1, U_2, U_3` in `U` with disjoint closures of `U_1, U_2`,
     some `g` has `g(U_1) ∩ U_3 = ∅` and `supp(g) ∩ U_2 = ∅`;
   - (iv) any two members of `U` lie in a common member.
2. **Simple groups.**  A countable simple group with a compressible action has no
   proper characters: its indecomposable characters are the trivial and the
   regular ones.
3. **Non-simple groups.**  Let `R` be an ICC subgroup of `G` with no proper
   characters such that, for every `g != e`, there are distinct
   `g_i in {h g h^-1 : h in R}` with `g_i^-1 g_j in R`.  Then every finite type
   factor representation of `G` is regular or factors through `G/N(R)`, where
   `N(R)` is the normal closure of `R`.
4. **Dyadic lemma.**  The dyadic intervals `(a, b)` with `[a, b] ⊂ (0, r)` form a
   base satisfying (i)--(iv) for the action of `F_(n,r)' = (F^0_(n,r))'` on
   `(0, r)`.  So that action is compressible.

Derivation: `dudko-medynets-compressible-action-character-theorems-citation`.
