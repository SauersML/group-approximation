---
rg: 2
id: g-x-free-set-actions-sofic-when-kernel-amenably-separable
kind: claim
title: An action of G1 x F on a coset space is sofic when the stabilizer meets G1 in an amenably separable subgroup
distinct_from:
  separating-sofic-quotient-sets-make-an-action-sofic: that proves the separation lemma (S1), product models (S2), separable and co-amenable-core stabilizers (C1, C2) and residually amenable Mikhailova ropes (C3); this adds a model for actor groups G1 x H in which G1 acts through an amenable quotient, and uses it to handle every stabilizer of G1 x F whose G1-kernel is amenably separable, with no hypothesis on the rest of the stabilizer.
  gkp-free-group-actions-are-sofic: that is GKP Theorem 2.19 for a single free actor; this adds a second commuting factor G1 whose kernel in the stabilizer is amenably separable.
  product-of-free-groups-set-actions-are-sofic: that asks for every action of F x F'; this settles all actions whose point stabilizers meet one of the two factors in an amenably separable subgroup, and so fences where a counterexample can live.
---

ESTABLISHED (unreviewed). Soficity of an action is GKP Definition 2.1(5).

Call a subgroup `N <= G` **amenably separable** if for every `a in G \ N`
there is a normal subgroup `M ⊴ G` with `G/M` amenable and `a ∉ NM`.
Examples: an intersection of finite-index subgroups; a normal subgroup with
residually amenable quotient; the trivial subgroup of a residually amenable
group.

**(A) Amenable-quotient factor.** Let `α : G_1 x H ↷ X` be an action on a
countable set. Suppose some `M ⊴ G_1` with `G_1/M` amenable acts trivially,
and the restriction `α|_H` is sofic. Then `α` is sofic.

**(B) Theorem.** Let `G_1` be a countable group and `F` a countable free group
(more generally, any countable group all of whose actions on countable sets
are sofic). Let `L <= G_1 x F` and `N = { a in G_1 : (a,1) in L }`. If `N` is
amenably separable in `G_1`, then `G_1 x F ↷ (G_1 x F)/L` is sofic.

DERIVATION [[g-x-free-set-actions-sofic-when-kernel-amenably-separable-proof]].

## Consequences for products of free groups

Let `F`, `F'` be countable free groups, `X` a countable `F x F'`-set, and
`L` the stabilizer of a point.

1. **One amenably separable kernel suffices.** If `L ∩ (F x 1)` is amenably
   separable in `F`, or `L ∩ (1 x F')` is amenably separable in `F'`, the orbit
   is sofic. By orbitwise soficity (GKP Propositions 2.15(2) and 2.16,
   [[gkp-sofic-action-toolkit]]) the same holds for `X` when it holds at one
   point of every orbit. Standard examples (M. Hall 1949, not re-read here):
   a finitely generated kernel is an intersection of finite-index subgroups.
2. **Free coordinate actions.** If `F x 1` acts freely on the orbit, then
   `L ∩ (F x 1) = 1`, which is separable because `F` is residually finite.
   So a nonsofic action of `F x F'` has **both** coordinate actions non-free,
   and both stabilizer kernels infinitely generated and not amenably separable.
3. **Pullbacks with a free residually amenable factor.** Let `P_1 x P_2 ↷ Y`
   be an action in which `P_1` acts freely, and `ρ_1 : F -> P_1`,
   `ρ_2 : F' -> P_2` homomorphisms with `ρ_1(F)` residually amenable. Then the
   pulled-back action of `F x F'` on `Y` is sofic. At any point
   `L ∩ (F x 1) = ker ρ_1`, which is normal with residually amenable quotient.
4. **The Kun–Thom Question 4.2 counterexample does not survive pullback.**
   [[commuting-sofic-actions-need-not-combine]] gives `G x G ↷ (G x G)/ΔΓ`,
   nonsofic, with both coordinate actions free and `G` residually finite. By
   (3), its pullback along any `φ_1 : F -> G`, `φ_2 : F' -> G` is a **sofic**
   action of `F x F'`. The same holds for pullbacks of any diagonal-coset
   action `(P x P)/ΔQ` with `P` residually amenable.
5. **Goursat subgroups.** Write `L` by Goursat's lemma as a fibre product over
   `Q ≅ p_1(L)/N_1 ≅ p_2(L)/N_2`. If `N_1` is normal in `F` with residually
   amenable quotient, the orbit is sofic, whatever the projections. With full
   projections this recovers (C3) of
   [[separating-sofic-quotient-sets-make-an-action-sofic]] for every countable
   residually amenable `Q`, finitely presented or not.

## What is left for a counterexample

A nonsofic set action of `F x F'` needs a stabilizer `L` whose two kernels
`N_1 = L ∩ F` and `N_2 = L ∩ F'` both fail amenable separability. For
full-projection Goursat subgroups over `Q` that means `Q` not residually
amenable. Exact finite models also dispose of LEF `Q` (the local-embedding
remark in the Attempts of [[product-of-free-groups-set-actions-are-sofic]]).
So the base must be neither residually amenable nor LEF, e.g. a nonsofic group.
