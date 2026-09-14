---
rg: 2
id: rf-groups-have-free-minimal-subshifts-with-finite-models-proof
kind: route
title: Nested holes meet each window at most once, and the unique cosets valued 1 and 2 separate every point from its translates
target: rf-groups-have-free-minimal-subshifts-with-finite-models
requires: []
artifacts:
  - research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md
---

Direct proof, artifact §3, parts (a)-(c).
- **(a) Finite models.** Take `FF^(-1) ∩ K_n = {e}`.
  - At most one `h_0 ∈ F` has `h_0σ ∈ K_n`, and the patterns of `x` at `σ` and `σk` (`k ∈ K_n`) agree off `h_0`.
  - The configuration `y_b`, equal to `x` off `K_n` and `b ∈ x(K_n)` on `K_n`, is `K_n`-invariant.
  - Its pattern at `σ` is the pattern of `x` at `σk` whenever `x(h_0σk) = b`. Conversely, the pattern of `x` at `σ` is that of `y_(x(h_0σ))`.
- **(b) Minimal.** The return set of a pattern contains:
  - `σK_n` if the window misses `K_n`;
  - `σK_(m+1)` if `h_0σ` has level `m ≥ n`;
  - `σ` times the `1`-coset of level `n` if `h_0σ = e`.
  Such a set is syndetic, so `x` is almost periodic.
- **(c) Free.** Let `g = σ^(-1)γσ` have level `m`. Pick the level-`m` coset `κK_(m+1)` valued `1` or `2` with `κg ∉ K_(m+1)`; at most one of the two fails.
  - For `ρ ∈ κK_(m+1)`, `ρg` lies in a different level-`m` coset, so `x(ρ) ≠ x(ρg)`.
  - Choose `ρ = hσ` with `h` in a transversal `T` of `K_n`. This is possible because `κK_(m+1)σ^(-1)` is a union of `K_n`-cosets.
  - So `(σx)(h) ≠ (γσx)(h)` with `h ∈ T`. Passing to limits over the finite set `T`, `γz ≠ z` for all `z ∈ X`. ∎
