---
rg: 2
id: rf-toeplitz-subshifts-over-residually-finite-groups-proof
kind: route
title: A single hole coset per level forces trivial stabilizers, and sparse fillings make every periodized window occur in the array
target: rf-toeplitz-subshifts-over-residually-finite-groups
requires: [rf-subshifts-are-periodic-window-approximable]
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part2.md
---

Artifact part 2, §6, Theorem T, with part 1 Lemma 3.
- **Setup.** `d_m = [Γ_(m-1):Γ_m] >= max(m+2, 2|B_(m-1)|+1)`; the hole `C_m` avoids `g_1,…,g_m`, so every
  element leaves the hole. (F1) `x` is constant on every skeleton `Γ_m`-coset. (F2) `x` takes both values on `C_m`.
- **Minimal.** The return set of `x|_W` contains `Γ_M` once `W ⊆ S_(<=M)`, so `x` is almost periodic.
- **Free orbit.** `g·x = x` sends the unique non-constant `Γ_m`-coset `C_m` to itself, so `g ∈ Γ_m` for every `m`,
  hence `g = e`. Dense free orbit gives topological freeness; minimal and infinite gives perfect.
- **RF.** Given `W`, choose `M` with `W ⊆ B_M` and all `W`-patterns of `X_Γ` realized by `x` inside `S_(<=M)`. Put
  `p_M = x` on `S_(<=M)`, `0` on `C_M`; it is `Γ_M`-periodic. For any `g`, the classes `γ̄ ∈ Γ_M/Γ_(M+1)` biject
  with the subcosets of `C_M` at each hole position, so at most `2|W| < d_(M+1)` classes are bad. A good `γ` makes
  the pattern of `x` at `γg` equal that of `p_M` at `g`. So the orbit of `p_M` lies in the window SFT and covers
  `L_W(X_Γ)`; Proposition S gives RF.
- **Measure.** Weak* limits of uniform measures on finite models (part 1, Lemma 3).
