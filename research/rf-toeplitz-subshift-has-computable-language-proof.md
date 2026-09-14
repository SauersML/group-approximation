---
rg: 2
id: rf-toeplitz-subshift-has-computable-language-proof
kind: route
title: Resolve a window at the level where its positions lie in distinct cosets, leaving one free position
target: rf-toeplitz-subshift-has-computable-language
requires: [effectively-rf-groups-have-computable-chains, rf-toeplitz-subshifts-over-residually-finite-groups]
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
---

Artifact §3, Theorem C. Write `C_m` for the hole coset of level `m`; the construction splits `C_{m-1}` into
`Δ_m`-cosets, one of which is `C_m`, one is valued `1`, and the rest are valued `0`.

**The language is the set of patterns of `x`.** The orbit of `x` is dense in `X_Δ` and a pattern is a clopen
condition, so a pattern occurs in `X_Δ` iff it occurs in `x`.

**Values are computable.** Given `γ` as a word, search `m = 1,2,…` for the first level with `γ ∉ C_m`. It halts
because `∩_m C_m = ∅`. Membership in `C_m` is decidable: `C_m` is one coset of `Δ_m`, and the construction computes
its representative level by level inside the computable finite quotients. At that level, `x(γ) = 1` if `γ` lies in
the `1`-coset of the level and `x(γ) = 0` otherwise.

**Occurrence is decidable.** Let `W = {w_1,…,w_r}` and `p ∈ A^W`. Search for `M` with `w_iw_j^{-1} ∉ Δ_M` for all
`i ≠ j`; it halts because `∩_m Δ_m = {e}`, and each test is decidable. Then the `w_i` lie in distinct `Δ_M`-cosets,
so for every `γ` at most one `w ∈ W` has `γw ∈ C_M`. Enumerate the finitely many cosets `γΔ_M` from the finite
quotient `Δ/Δ_M`. For each:

- every `w` with `γw ∉ C_M` has `x(γw)` determined by the coset `γΔ_M`, computed as above;
- the at most one `w` with `γw ∈ C_M` is unconstrained. Replacing `γ` by `γδ` with `δ ∈ Δ_M` does not change the
  determined values, and `C_M` splits at level `M+1` into a hole, a `1`-coset and at least one `0`-coset, so both
  letters are realized at that position.

So `p` occurs iff for some coset representative it agrees with the computed values at the determined positions, a
finite decidable check. ∎
