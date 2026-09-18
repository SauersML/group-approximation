---
rg: 2
id: f2-cayley-dominance-from-bounded-mass-harper-relaxation
kind: route
title: Every set's spectral law lies in the (M)+(H) relaxation and has the same displacement profile, so a bound on the relaxation bounds the subgroup-dominance constant of every set
target: f2-cayley-subgroup-sets-are-constant-factor-optimal
requires:
  - f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds
  - f2-cayley-mass-harper-spectral-relaxation-is-bounded
---

Let `S` be a subset of `F_2^k` with `|S| = 2^(k-c)`, and let `nu_S = N hat(1_S)^2 / |S|`.

1. `nu_S(0) = N (|S|/N)^2 / |S| = 2^-c`.
2. `nu_S` satisfies (M) and (H), by
   `f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds`. So `nu_S` lies
   in `F(k, c)`.
3. `d_(nu_S)(a) = 2 nu_S{chi.a = 1} = d_S(a)` for every `a` (same claim). So the
   LPs defining `C(nu_S)` and `C(S)` coincide, including the convention at
   `d = 0`, and `C(S) = C(nu_S) <= R_MH(k, c) <= R_MH`.

So `C* <= R_MH < infinity`. The weak forms transfer in the same way, because
`Phi_w(S) = Phi_w(nu_S)` for every `w`.
