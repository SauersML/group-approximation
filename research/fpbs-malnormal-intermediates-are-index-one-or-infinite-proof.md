---
rg: 2
id: fpbs-malnormal-intermediates-are-index-one-or-infinite-proof
kind: route
title: The coset set of a finite-index class gives a K-invariant finite measure on finite subsets of K\L, whose finite orbits contradict malnormality
target: fpbs-malnormal-intermediates-are-index-one-or-infinite
requires: []
artifacts:
  - research/artifacts/fpbs-mal-normal-and-intermediate-class-kills-2026-09-20.md
---

Self-contained. The full proof is §3 of the artifact.

1. **Setup.** Suppose `X_m` has positive measure for some `2 <= m < infinity`.
   Here `X_m` is the set of points whose `T`-class contains exactly `m`
   `E_K`-classes. It is Borel and `T`-invariant.
2. **The coset map.** Put `S_x = { g in L : g x T x }`.
   - Freeness makes `g` unique for each point, and `E_K ⊆ T` makes `S_x` a
     union of `m` right cosets of `K`, one of which is `K`.
   - For `k in K`, `S_{kx} = S_x k^{-1}`.
   - So `F(x) = K\S_x` is a Borel map from `X_m` to the countable set of
     `m`-subsets of `K\L`, and `F(kx) = F(x) k^{-1}`.
3. **The invariant measure.** `F_*(mu|X_m)` is a nonzero finite `K`-invariant
   measure on a countable set. So an atom `ω` has a finite orbit, and its
   stabiliser `K_ω` has finite index in `K`.
4. **The contradiction.** The pointwise stabiliser `K'` of the `m` cosets in
   `ω` has finite index in `K_ω`, so it is infinite. For a coset `K g` in `ω`
   with `g ∉ K`, every `k in K'` satisfies `g k g^{-1} in K`. So
   `K' ⊆ g^{-1} K g ∩ K = {1}`, which is a contradiction.
