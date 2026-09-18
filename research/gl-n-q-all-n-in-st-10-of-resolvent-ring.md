---
rg: 2
id: gl-n-q-all-n-in-st-10-of-resolvent-ring
kind: route
title: One finitely presented Kazhdan group St_10(R_L) contains GL_n(Q) for every n
target: gl-n-q-explicit-natural-fp-overgroup
requires:
  - leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1
  - leavitt-resolvent-ring-is-fp-and-contains-q
  - steinberg-groups-of-fp-rings-are-fp-in-rank-five
artifacts:
  - research/artifacts/gq-steinberg-q-krstic-mccool-source.md
---

Put `Γ = St_10(R_L)`, where `R_L` is the ring of
`leavitt-resolvent-ring-is-fp-and-contains-q`.

- **Finitely presented.** `Γ` is finitely presented with an explicit presentation, since
  `10 >= 5` (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`, refereed by a and b).
  Property (T) comes from `steinberg-finite-presentation-and-kazhdan-theorem`; it is not
  needed for the target.
- **Contains every GL_n(Q).** `Q ⊆ R_L`, and `R_L` carries a Leavitt pair. So part 2 of
  `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1` puts every `GL_n(Q)` into `Γ`.
- **Presentation.** Fully explicit: the rank-five node's presentation of `St_10(F_6)` (630
  generators; relation families (B1), (B2)), plus the nine relator words. As in
  `gl-n-q-explicit-via-steinberg-group-of-resolvent-ring`:
  `Γ = St_10(F_6)/⟨⟨x_12(ρ_1), …, x_12(ρ_9)⟩⟩`, with the nine relator words written there
  (`st-n-of-ring-quotient-adds-one-relator-per-ideal-generator`).

This improves the rank-`(6n+7)` route in two ways: there is one group for all `n`, and a
fixed rank of 10. It is not simple.

**Lean (2026-09-18).** This route is kernel-checked in Lean 4 with Mathlib, with no
hypotheses and only the axioms `propext`, `Classical.choice` and `Quot.sound`:
`GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q` in
`GroupApproximation/SteinbergFP/Challenge.lean` (2539180c0). That file states the result
over `R_L` as a `RingQuot` of `ℤ⟨Fin 6⟩` by the nine relations, and over `St_10` presented on
symbols `x_ij(r)`. These are the exact definitions of the Palomar Boone–Higman
challenge. The proof has four parts, which follow the required nodes:
- **Finite presentation.** `steinberg_isFinitelyPresented` (`ResolventRing.lean`) gives
  `St_{d+5}(R_L)` for every `d`, as `St(ℤ⟨Fin 6⟩)` modulo the normal closure of the nine
  relators.
- **Faithful module.** `R_L` acts on `ℕ → ℚ` (`Model.lean`), so `R_L ≠ 0` and `ℚ` embeds in
  the center of `R_L` (`ratHomCenter`, `ResolventRing.lean`).
- **Embedding.** The Leavitt swindle `exists_injective_elementary` (`Swindle.lean`): for any
  ring `S` with a binary Leavitt pair and any injective `φ : F →+* S` whose image commutes
  with `t_0, t_1`, the elementary group `E_V(F)` embeds in `St_{3|V|+1}(S)` whenever `St_V(F)`
  is perfect.
- **Rank collapse.** `GL_n(ℚ) ↪ E_{3k}(ℚ) ≅ E_3(M_k(ℚ))` (needs `2n ≤ 3k`) and `M_k(R_L) ≅ R_L`
  for `k = 2^n`, with `V = Fin 3`, so `3|V| + 1 = 10` (`Morita.lean`, `Embedding.lean`).

Lesson for general BH: the embedding half of every Leavitt ring host is now closed in
Lean, and it does not depend on rank. The swindle names no field. It needs only an injective
ring map from `F` into a ring `S` with a Leavitt pair commuting with its image, and a perfect
`St_V(F)`. When `S` is finitely presented, every `St_n(S)` with `n ≥ 5` is finitely presented
too. So for an input inside some `E_V(F)` of that kind, BH owes only a simple quotient of
`St(S)` that keeps the input: the K-gate, not the embedding.
