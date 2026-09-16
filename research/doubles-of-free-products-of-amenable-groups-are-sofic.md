---
rg: 2
id: doubles-of-free-products-of-amenable-groups-are-sofic
kind: claim
title: Every symmetric double of a free product of amenable groups over any subgroup is sofic, and the vertex inclusion is RE/C
distinct_from:
  free-group-doubles-over-any-subgroup-are-sofic: that is the case of a free vertex group; this allows any group all of whose set actions are sofic, including finitely presented vertex groups with torsion that are not residually finite, where no separability argument is available even for finitely generated subgroups
  sofic-coset-action-makes-amalgam-double-sofic: that is the general theorem with a sofic-coset-action hypothesis; this is the class of vertex groups for which that hypothesis holds for every subgroup at once
---

Let `H` be a countable group all of whose actions on countable sets are sofic
(the class `𝒜` of `all-actions-sofic-groups-closed-under-free-products`). For
example, `H` can be any countable free product `*_i K_i` of amenable groups.
Let `Γ ≤ H` be an arbitrary subgroup. Then:

1. the symmetric amalgamated double `D = H *_Γ H` is sofic;
2. `L(H) *_(L(Γ)) L(H) = L(D)` is Connes embeddable;
3. the inclusion `L(Γ) ⊂ L(H)` is relatively embeddable over the scalars
   (`RE/C`).

**What is new.** Take `H = Γ_p * Z` with `Γ_p` the finitely presented
amenable Abels--Pruefer quotient. This `H` is finitely presented and not
residually finite. The classical route (a separable subgroup of a residually
finite group has a residually finite double) is therefore unavailable, even
for finitely generated `Γ`. The free-actor node covers only free `H`.

**Firewall reading for the root lane.**
- An obstruction to `RE/C` for a pair `C ≤ A` needs `A ∉ 𝒜`, and no
  `𝒜`-subgroup of `A` can carry the obstruction for its own subgroups.
- For the arithmetic pairs of `non-hyperlinear-from-non-relative-embeddability`,
  `A = SL_n(Z[1/2])` is not a nontrivial free product. For `n = 2` it has
  the nontrivial center `{±I}`. For `n = 3` it has property (T), hence
  property FA. Its membership in `𝒜` is not decided here, so this node says
  nothing about those pairs.

DERIVATION
doubles-of-free-products-of-amenable-groups-proof
