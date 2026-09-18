---
rg: 2
id: twisted-bt-point-fixing-actor-elements-are-divisible
kind: claim
title: In a twisted Brin-Thompson group SV_G every infinite-order element that ignores one coordinate, in particular every infinite-order g in G fixing a point of S, lies in a copy of Q
distinct_from:
  rationals-embed-in-brin-thompson-group-2v: that is the case G = 1 on two coordinates (nV), due to Kojima--Sheng; this claim is the same device in every twisted Brin--Thompson group, applied to elements that permute coordinates.
  twisted-brin-thompson-finite-presentation-criterion: that is Zaremsky's finite presentation criterion, used here for the corollary; this claim adds divisibility inside the resulting simple groups.
  gl-n-q-embeds-in-fp-simple-group: that is the root; this claim gives divisible hulls of abelian subgroups of an actor, not the non-abelian rational groups the root needs.
artifacts:
  - research/artifacts/gq-bt-kojima-mechanism.md
---

**ESTABLISHED** through `twisted-bt-point-fixing-actor-elements-are-divisible-proof`
(lane proof, not independently reviewed).

**Setting.** `G` acts faithfully on a nonempty set `S`. As in survey
arXiv:2306.16356v3, §4, `SV_G` is "the group of all homeomorphisms of `C^S`
that locally agree with elements of the restricted wreath product
`V wr G = (⊕_S V) ⋊ G`". Here `G` acts on `C^S` by permuting coordinates, so
`G <= SV_G`.

**Statement.**
1. Fix `* ∈ S` and write `C^S = C_* × C^(S \ {*})`. Let `h ∈ SV_G` have
   infinite order and satisfy `h = id_(C_*) × h'` for a homeomorphism `h'` of
   `C^(S \ {*})`. Then `h` lies in a subgroup of `SV_G` isomorphic to `(Q,+)`.
   This applies to every `g ∈ G` of infinite order with `g(*) = *`.
2. Let `g_1, …, g_k ∈ G` commute pairwise and fix points `*_1, …, *_k ∈ S`
   pairwise distinct, each `g_i` fixing every `*_j`. If `<g_1, …, g_k> ≅ Z^k`,
   then it lies in a subgroup of `SV_G` isomorphic to `Q^k`.
3. **Corollary.** Let `G ↷ S` be of type (A)
   (`type-a-action-gives-boone-higman-for-subgroups`), with `|S| >= 2`, and let
   `S^+ = S ⊔ {*_1, …, *_k}` with the new points fixed.
   - `G ↷ S^+` is again of type (A).
   - So `Γ = S^+V_G` is a finitely presented simple group containing `G`
     (`twisted-brin-thompson-finite-presentation-criterion`).
   - In `Γ`, any `k` pairwise commuting elements of `G` generating `Z^k` extend
     to a copy of `Q^k`.

**Limits (see the artifact).** The roots are localized. If `h' ∈ G` does not
commute with `g`, the commutator `[r, h']` of a root `r` of `g` acts only on
the overflow slab of the register. It is not a root of `[g, h']`. So the
device yields rational hulls of abelian subgroups only. It gives no
`U_3(Q)`, no `Aff(Q)`, and no Steinberg relations of `SL_n(Q)`.
