---
rg: 2
id: root-subgroups-over-crossed-products-not-confined-proof
kind: route
title: Conjugating a root subgroup by e_31(u^N) gives pairwise trivially intersecting conjugates, so it is not confined
target: elementary-root-subgroups-over-crossed-products-are-not-confined
requires: []
---

**Lemma A.** Let `H ≤ G`. Suppose there are `k_1, k_2, … ∈ G` with `k_m H k_m^{-1} ∩ k_l H k_l^{-1} = {1}` for `m ≠ l`.
Then `H` is not confined.

*Proof.* Let `P ⊆ G \ {1}` be finite. Each `p ∈ P` lies in at most one conjugate `k_m H k_m^{-1}`, so some `m` has
`k_m H k_m^{-1} ∩ P = ∅`. ∎

**Lemma B.** For every `N ≠ M` in `Z`, `u^N − u^M` is a left non-zero-divisor in `R`.

*Proof.* `u^N − u^M = u^M(u^{N−M} − 1)` with `u^M` a unit, so it suffices that `(u^d − 1)r = 0` forces `r = 0` for `d ≠ 0`.
Write `r = Σ_{j∈S} f_j u^j` with `S` finite and every `f_j ≠ 0`. Then `u^d r = Σ_j (f_j∘T^{-d}) u^{j+d}`. If `d > 0` and
`r ≠ 0`, the exponent `max S + d` occurs in `u^d r` with a nonzero coefficient and does not occur in `r`, so `u^d r ≠ r`.
The case `d < 0` uses `min S`. ∎

**Proof of the claim.** Subgroups of a non-confined subgroup are not confined, since a set confining `K ≤ H` also
confines `H`. Confinement is invariant under conjugation, and signed permutation matrices lie in `EL_n(R)` and move
`e_12(R)` to any `e_ij(R)`. So it suffices to take `H = e_12(R)`, with indices `1,2,3` inside `n ≥ 3`.

Put `k_N = e_31(u^N)`, `N ≥ 0`. With `[g,h] = ghg^{-1}h^{-1}`, the Steinberg relation for distinct indices `3,1,2` gives
`[e_31(s), e_12(r)] = e_32(sr)`. So
`k_N e_12(r) k_N^{-1} = [k_N, e_12(r)]·e_12(r) = e_32(u^N r) e_12(r) = I + u^N r E_32 + r E_12`,
because `E_32 E_12 = 0`. Suppose `e_32(u^N r)e_12(r) = e_32(u^M r')e_12(r')` with `N ≠ M`. Comparing the `(1,2)`
entries gives `r = r'`, and comparing the `(3,2)` entries gives `(u^N − u^M) r = 0`. By Lemma B, `r = 0`. So the conjugates
`k_N H k_N^{-1}` intersect pairwise trivially, and Lemma A applies. ∎

**Model tests.**
- A finite group `G` has no infinite sequence of pairwise trivially intersecting conjugates of a nontrivial subgroup,
  and indeed every subgroup of a finite group is confined (take `P = G∖{1}`).
- Lemma B fails in `M_N(k)` models, where `P^N = 1`. That matches the fact that there the root subgroup is confined.
