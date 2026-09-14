---
rg: 2
id: generic-rotation-codings-of-zd-are-window-periodic
kind: claim
title: Codings of free circle rotations of Z^d by intervals with generic endpoints are free minimal residually finite subshifts, so they give simple Kazhdan LEF groups
distinct_from:
  labbe-shift-is-a-toral-rotation-coding: that is a toral rotation coding through a Markov partition, which is an SFT without periodic points and so not residually finite; this is a coding through a generic partition, whose stable cell structure gives exact periodic models.
  rf-toeplitz-subshifts-over-residually-finite-groups: that builds residually finite Toeplitz subshifts, which are almost one-to-one extensions of odometers; this gives almost one-to-one extensions of irrational rotations, a zero-entropy family with a continuous rather than profinite maximal equicontinuous factor.
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed; route `generic-rotation-codings-of-zd-are-window-periodic-proof`, artifact §7).**

**Statement.**
- Let `α ∈ R^d` with `1, α_1, …, α_d` rationally independent, `m >= 2`, and `0 = β_0 < … < β_(m-1) < 1` with `β_i − β_j ∉ Z + ⟨Z^d, α⟩` for `i ≠ j`.
- Put `x_t(v) = i` when `t + ⟨v,α⟩ ∈ [β_i, β_(i+1))` mod 1, and let `X` be the closure of the codings `x_t`.

Then `X ⊆ {0,…,m−1}^(Z^d)` is a free minimal subshift that is window-periodic, hence residually finite (Kerr–Nowak). So for every prime power `q` and `N >= 3`, `EL_N(LC(X,F_q) ⋊ Z^d)/Z` is an infinite, finitely generated, simple, Kazhdan, LEF group.

**Proof idea.**
- The `W`-patterns of `X` are the labels of the arcs cut out by the `m|W|` distinct points `β_i − ⟨w,α⟩`.
- Replacing `α` by `round(Nα)/N` keeps their cyclic order for large `N`. The finite orbit `t_0 + (1/N)Z` then realizes exactly the same patterns.

**Contrast.** Labbé's shift is also a rotation coding, but through a Markov partition, and it is not residually finite. Whether a rotation coding has exact finite models is a property of the partition geometry, not of the rotation.

**Credit.** Two-dimensional Sturmian configurations: Berthé–Vuillon (2000). The periodic approximation is probably folklore; the literature check is bounded.
