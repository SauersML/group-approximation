---
rg: 2
id: rf-groups-have-free-minimal-subshifts-with-finite-models
kind: claim
title: Every finitely generated infinite residually finite group acts freely and minimally on a three-letter Toeplitz subshift that is a limit of finite subshifts
distinct_from:
  rf-toeplitz-subshifts-over-residually-finite-groups: that builds a binary Toeplitz array with moving holes, large successive indices and a union bound; this uses nested holes K_m containing the identity, index at least 3 and three letters, so a window meets the hole at most once and freeness at every point follows from two unique cosets per level.
artifacts:
  - research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be finitely generated, infinite and residually finite, acting on `{0,1,2}^Γ` by `(γx)(h) = x(hγ)`. Choose normal subgroups `Γ = K_0 > K_1 > ⋯` of finite index with `∩ K_m = {e}` and `[K_m : K_(m+1)] ≥ 3`. Let `x` satisfy:
- `x(e) = 1`;
- on `K_m \ K_(m+1)` it is constant on `K_(m+1)`-cosets, with the values `1` and `2` each on exactly one coset and `0` on the rest.

Then the orbit closure `X` of `x` is infinite and minimal, `Γ` acts freely at every point, and `X` has finite models. For every finite `F` there is `n` such that the configurations equal to `x` off `K_n` and constant on `K_n` generate a finite subshift with the `F`-patterns of `X`.

**Proof** (artifact §3).
- `x(hk) = x(h)` for `h ∉ K_n` and `k ∈ K_n`.
- **Finite models.** If `FF^(-1) ∩ K_n = {e}`, each window `Fσ` meets `K_n` at most once, and there `x(hσk)`, `k ∈ K_n`, runs over `x(K_n)`.
- **Minimal.** Each pattern recurs along a coset of some `K_m`.
- **Free.** For `γ ∉ K_n`, let `m` be the level of `σ^(-1)γσ`. One of the two level-`m` cosets valued `1` and `2` contains `hσ` with `h` in a fixed transversal of `K_n` and `x(hσ) ≠ x(hγσ)`. Limits then show that `γ` fixes no point of `X`.

Uses: `finite-model-subshift-elementary-groups-simple-kazhdan-lef` (e.g. `Γ = SL_3(Z)`), and the converse `free-subshift-with-finite-models-forces-rf-group`.

Credit: Toeplitz arrays over residually finite groups are due to Krieger and to Cortez–Petite. The nested-hole design is elementary; no literature check was run beyond the repository graph.

Route: `rf-groups-have-free-minimal-subshifts-with-finite-models-proof`.

**Review (sk-verify-4, 2026-09-13): PASS.** Key identity x(hk) = x(h), finite models y_b, syndetic return sets, and freeness through the special level cosets (m = ℓ(γ) by normality; K_n ⊆ K_(m+1)) re-derived. See `research/artifacts/sk-review-4-2026-09-13-part1.md` §8.
