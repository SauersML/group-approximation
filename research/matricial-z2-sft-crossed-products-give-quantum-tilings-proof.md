---
rg: 2
id: matricial-z2-sft-crossed-products-give-quantum-tilings-proof
kind: route
title: Exact matrix models restrict to covariant families; conversely the crossed product is the colimit of the local presentations
target: matricial-z2-sft-crossed-products-give-quantum-tilings
requires: [simple-rings-with-local-matrix-models-are-matricial]
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part2.md
---

Artifact part 2, §5.

**Matricial ⇒ families.**
- Fix an `n` in the ω-set where `ψ_n` is exact on the finitely many identities of `R_Ω`: partition of
  unity, orthogonality, commutation of `u_z χ_[a] u_z^(-1)` with `χ_[b]` for `|z| <= 2D`, vanishing of
  forbidden products on `B_D`, and `u_(e_1) u_(e_2) = u_(e_2) u_(e_1)`.
- Put `W = k^(N_n)`, `U_i = ψ_n(u_(e_i))` and `E_a(0) = ψ_n(χ_[a])`. Conjugating by `U^z` gives
  (Q1)–(Q3) at every `z`.

**Families ⇒ matricial.**
- Let `𝒜_D` be the `k`-algebra presented by `E_a(z)`, `U_i^(±1)` and the covariant (Q1)–(Q3) at
  scale `D`. The maps `𝒜_D -> 𝒜_(D+1) -> R_Ω` are surjective.
- The colimit is `R_Ω`: all idempotents commute and all non-occurring patterns vanish, so the
  coefficient algebra is `LC(Ω,k)`, and normal forms map injectively.
- A finite window of `R_Ω` has finitely many identities, each holding at some finite stage. So for
  large `D_n` a finite-dimensional `𝒜_(D_n)`-module gives a unital map that is exact on the window.
- `R_Ω` is simple, since the action is free and minimal (artifact part 1, Lemma 2.1).
  `simple-rings-with-local-matrix-models-are-matricial` then gives the embedding.
