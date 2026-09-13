---
rg: 2
id: leavitt-triangular-units-have-linear-depth-growth-proof
kind: route
title: The degree-zero part of a triangular unit has finite order, and a unipotent power squares into ever lower degree
target: leavitt-triangular-units-have-linear-depth-growth
requires: []
artifacts: [research/artifacts/leavitt-unit-depth-growth-lemmas-2026-09-13.md]
---

Full text: Proposition 4 of `research/artifacts/leavitt-unit-depth-growth-lemmas-2026-09-13.md`.

1. **Conjugation.** `ell(xy) <= ell(x) + ell(y)` gives
   `D_(huh^(-1))(m) <= D_u(m) + 2 max(ell(h), ell(h^(-1)))`, so `lambda` is a conjugacy invariant. Take `u` in
   `H_<=`. For `H_>=`, apply the anti-automorphism `s_μ t_ν -> s_ν t_μ`, which preserves `ell` and inverts
   degrees, together with `u -> (u*)^(-1)`.
2. **Degree zero.** `x -> x_0` is a ring map `⊕_(k<=0) R_k -> R_0`. So `u_0` is a unit of the locally finite
   algebra `R_0`, of finite order `r`.
3. **Unipotent power.** `v = u^r` has `v_0 = 1`, so `v = 1 + n` with `n` of degrees `<= -1`. In characteristic
   two, `v^(2^k) = 1 + n^(2^k)`, and `n^(2^k)` has all degrees `<= -2^k`.
4. **Growth.**
   - `u` has infinite order, so `n^(2^k) != 0`.
   - A nonzero element of degrees `<= -2^k` contains a monomial `s_μ t_ν` with `|ν| >= 2^k`. So
     `ell(v^(2^k)) >= 2^k`.
   - `D_v` is subadditive, so `lambda(v) >= 1`.
   - `lambda(u^r) = r lambda(u)`, so `lambda(u) >= 1/r`. ∎
