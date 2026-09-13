---
rg: 2
id: abstract-btb-pairs-fp-and-relatively-simple
kind: claim
title: For a type [A_2] action the abstract twisted Brin--Thompson group is finitely presented and relatively simple, and the actor pair embeds in it
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that is the finite-presentation criterion, stated for every action and cross-checked against FFWZ Theorem B, so item 1 here restates it at type [A_2]; this adds relative simplicity of SV_G for non-faithful actions, where SV_G is not simple, and the pair embedding of the actor.
  abstract-btb-simple-quotient-fp-gate: that compares finite presentation of the simple quotient with finite presentation of the action image; this records finite presentation and relative simplicity of the abstract group itself, and the pair embedding of the actor.
  boone-higman-implies-relative-permutational-bh: that is FFWZ Theorem C, placing a Boone--Higman group in some type [A_2] actor; this holds for every type [A_2] action and turns sharp embeddings in actor pairs into sharp embeddings in finitely presented relatively simple groups.
artifacts:
  - research/artifacts/bh-simple-products-embed-2026-09-12.md
---

**ESTABLISHED (literature import)** by
`abstract-btb-pairs-fp-and-relatively-simple-citation`.

Let a group `G` act on a non-empty set `S` with type [A_2], and let
`K = ker(G ↷ S)`. Let `SV_G` be the abstract twisted Brin--Thompson group, and
`SK_G = ker(SV_G → SV_{G/K})` its canonical kernel. Then:
1. **Finite presentation.** `SV_G` is finitely presented (FFWZ Theorem 4.1(ii)).
2. **Relative simplicity.** `(SV_G, SK_G)` is relatively simple (Theorem 3.6).
   So `SK_G` is proper and contains every proper normal subgroup of `SV_G`, and
   `SV_G/SK_G = SV_{G/K}` is simple.
3. **Pair embedding.** `λ: g ↦ [·,id,g,·]` is injective with
   `λ(G) ∩ SK_G = λ(K)` (Lemma 5.2).

Type [A_2] and embeddings of pairs are as in
`relative-pbh-closed-under-finite-direct-products`. Items 2 and 3 hold for every
action; only item 1 uses type [A_2].

**Consequence.** Let `Γ ≤ G` with `Γ ∩ K = 1`. Then
`λ(Γ) ∩ SK_G = λ(Γ) ∩ λ(G) ∩ SK_G = λ(Γ ∩ K) = 1`. So `Γ` sharply embeds in the
finitely presented relatively simple group `SV_G`, and it embeds in the simple
group `SV_{G/K}`. This is FFWZ's "hence" after Conjecture 1.8, stated for an
arbitrary type [A_2] action.

**Not claimed.** `SV_{G/K}` need not be finitely presented. By FFWZ Corollary 4.2
it is finitely presented exactly when `G/K` is
(`abstract-btb-simple-quotient-fp-gate`).
