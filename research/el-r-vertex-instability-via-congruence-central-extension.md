---
rg: 2
id: el-r-vertex-instability-via-congruence-central-extension
kind: route
title: A congruence subgroup of SL_3(F_q[t]) with a visible Kazhdan central Z-extension makes the rank-3 Kun--Thom vertex flexibly unstable
target: el-r-polynomial-vertex-not-flexibly-hs-stable
requires:
  - sl3-polynomial-finite-index-z-extension-center-survives
  - bdhv-central-extension-property-t
  - kazhdan-cover-models-round-iff-kernel-fixed-mass-one
  - flexible-hs-stability-descends-to-retracts-finite-index
---

**Derivation, conditional on the open premise.**

1. **The models.** By `sl3-polynomial-finite-index-z-extension-center-survives`, fix
   `Δ <= SL_3(F_q[t])` of finite index and `1 -> ⟨z⟩ -> Δ~ -> Δ -> 1`, where `Δ~` has finite
   abelianization and finite quotients `Q_k` in which `z̄` has order `n_k -> ∞`.
   - `Δ` is Kazhdan: it has finite index in the Kazhdan group `SL_3(F_q[t])`, which is a quotient
     of `EL_3` over a finitely generated ring.
   - `Δ~` is Kazhdan by `bdhv-central-extension-property-t`.
   - Let `ρ_k` be the left regular representation of `Q_k`, restricted to the subspace where `z̄`
     acts by `e^(2πi/n_k)`, and pulled back to `Δ~`.
2. **No rounding.**
   - For `m = z^j`, `||ρ_k(m) - 1||_2 = |e^(2πij/n_k) - 1| -> 0`, so (KC1) holds with `N = ⟨z⟩`.
   - `Fix_N(ρ_k) = 0`.
   - By `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`, no subsequence of the models
     `ρ_k∘s` of `Δ` rounds flexibly.
3. **Up to the vertex.** By `flexible-hs-stability-descends-to-retracts-finite-index`:
   - item 2 (finite index in a Kazhdan group) makes `SL_3(F_q[t])` not flexibly HS-stable;
   - item 1, applied to the retract `x_1 -> t`, `x_j -> 0`, makes `EL_3(F_q[x_1..x_d])` not
     flexibly HS-stable for every `d >= 3`.

**Premise gap.** Property (T) of `SL_3(F_q[t])` is used in step 1 as a known input: it is the
`r = 3`, `d = 1` case of the Ershov--Jaikin-Zapirain theorem that `EL_r` over finitely generated
rings is Kazhdan for `r >= 3`. It is not a separate `requires` entry, because the graph records it
only inside the vertex nodes. The route stays unfired while its premise claim is open.
