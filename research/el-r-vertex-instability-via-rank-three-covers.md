---
rg: 2
id: el-r-vertex-instability-via-rank-three-covers
kind: route
title: Extra finite quotients of the finitely presented covers of SL_3(F_q[t]) make the rank-3 Kun--Thom vertex flexibly unstable
target: el-r-polynomial-vertex-not-flexibly-hs-stable
requires:
  - kazhdan-cover-models-round-iff-kernel-fixed-mass-one
  - sl3-polynomial-covers-have-extra-finite-quotients
---

**Derivation, conditional on the open premise.**

1. **Rank 3 is instability at `SL_3(F_q[t])`.** By `sl3-polynomial-covers-have-extra-finite-quotients`,
   some finitely presented Kazhdan cover of `SL_3(F_q[t])` has truncations `Γ_L`, with infinitely
   many carrying a finite quotient in which `K_L = ker(Γ_L -> SL_3(F_q[t]))` survives. The left
   regular representation of that quotient is nontrivial on `K_L`. The corollary of
   `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` then gives an asymptotic representation
   of `SL_3(F_q[t])` with no flexible rounding. The models are exact on larger and larger balls.

2. **Retract.**
   - Let `i : SL_3(F_q[t]) -> Γ = EL_3(F_q[x_1..x_d])` be induced by `t -> x_1`, and
     `r : Γ -> SL_3(F_q[t])` by `x_1 -> t`, `x_j -> 0` for `j >= 2`. Both are ring maps, hence
     group homomorphisms, and `r∘i = id`. Also `EL_3(F_q[t]) = SL_3(F_q[t])`, since `F_q[t]` is
     Euclidean.
   - If `α_n` is an asymptotic representation of `SL_3(F_q[t])`, then `α_n∘r` is one of `Γ`.
   - Suppose genuine `π_n` of `Γ` round `α_n∘r`. Then `π_n∘i` are genuine representations of
     `SL_3(F_q[t])`, and `||α_n(h) - Pπ_n(i(h))P*||_2 = ||(α_n∘r)(i(h)) - Pπ_n(i(h))P*||_2 -> 0`.
   - So a non-roundable model of `SL_3(F_q[t])` yields the non-roundable model `α_n∘r` of `Γ`.

3. **Conclusion.** For `r = 3` and every `d >= 3` and `q`, `EL_3(F_q[x_1..x_d])` is not flexibly
   HS-stable.

**Scope.** The models are not claimed to extend to the actor `G`. This route does not touch
`hs-stable-vertex-rounding-for-every-model`, whose models must extend.
