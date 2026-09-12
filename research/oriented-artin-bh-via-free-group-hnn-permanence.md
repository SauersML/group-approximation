---
rg: 2
id: oriented-artin-bh-via-free-group-hnn-permanence
kind: route
title: Fold Jankiewicz's amalgam over free groups into an HNN extension of a free group over decidable edges
target: admissibly-oriented-artin-groups-satisfy-boone-higman
requires:
  - admissibly-oriented-artin-groups-split-over-free-groups
  - bh-embeddability-survives-decidable-edge-hnn
---

Let Γ admit an admissible partial orientation. By
`admissibly-oriented-artin-groups-split-over-free-groups`, one of two cases
holds.

**Case HNN.** `Art_Γ = A*_φ`, with `A` free of finite rank and associated
subgroups `C_1, C_2 <= A` free of finite rank.
- `A` embeds in a finitely presented simple group: it embeds in `F_2`, and
  `F_2 <= SL_2(Z) <= GL_2(Z)`, which embeds in one by Scott (survey
  arXiv:2306.16356v3, Theorem 5.1(1)).
- Finitely generated subgroups of a free group have decidable membership, by
  Stallings foldings.
- So `bh-embeddability-survives-decidable-edge-hnn` applies directly.

**Case amalgam.** `Art_Γ = A ∗_C B`, with `A, B, C` free of finite rank and
injections `i : C -> A`, `j : C -> B`.
1. **The HNN extension.** Let `G = A ∗ B`, free of finite rank. Put
   `C_1 = i(C)`, `C_2 = j(C)` and `φ = j ∘ i^-1 : C_1 -> C_2`, given on
   generators. Both subgroups are finitely generated in the free group `G`, so
   membership in them is decidable, and `G` embeds in a finitely presented simple
   group as above. By `bh-embeddability-survives-decidable-edge-hnn`, the HNN
   extension `H = G*_φ = < G, t | t c t^-1 = φ(c), c ∈ C_1 >` embeds in a
   finitely presented simple group.
2. **The map.** Define `ψ : A ∗_C B -> H` by `a |-> a` and `b |-> t^-1 b t`. It
   is well defined, because for `c ∈ C`
   `ψ(j(c)) = t^-1 φ(i(c)) t = i(c) = ψ(i(c))`.
3. **Injectivity.** Take a reduced alternating word
   `g = a_1 b_1 a_2 b_2 ...`, with `a_k ∈ A - i(C)` and `b_k ∈ B - j(C)`, and
   possibly an extra letter at either end. Its image
   `a_1 t^-1 b_1 t a_2 t^-1 b_2 t ...` contains no pinch:
   - `t^-1 x t` pinches only when `x ∈ C_2`, and `b_k ∉ j(C) = C_2`;
   - `t x t^-1` pinches only when `x ∈ C_1`, and `a_k ∉ i(C) = C_1`.
   By Britton's lemma the image is nontrivial whenever it contains `t`. A word
   of length one is a nontrivial element of `A` or of `B`, and its image is
   nontrivial in `G`, or conjugate to one that is. So `ψ` is injective.
4. **Conclusion.** `Art_Γ <= H`, and `Art_Γ` embeds in a finitely presented
   simple group. QED
