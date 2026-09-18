---
rg: 2
id: unimodular-line-pairs-detect-cyclic-quotients-proof
kind: route
title: Compute the quotient of R^N by the sum of the standard line and a transvected line, and read idempotent classes in K_0
target: unimodular-line-pairs-detect-cyclic-quotients
requires: []
---

**Item 1.**
- `w = e_1 + e_2 b` is unimodular, since the row `(1, 0, ..., 0)` gives `(1,0,...,0) w = 1`. Also
  `w = x_21(b) e_1`, so `L_b = x_21(b)(e_1 R)` lies in `Ω_N^0`.
- `w in e_1 R` would force `b = 0`. So `L_b != e_1 R`.
- `e_1 R + L_b = {(t + s, bs, 0, ..., 0)} = {(t', bs, 0, ..., 0) : t', s in R}`.
- The map `R^N -> R/bR ⊕ R^(N-2)`, `(r_1, r_2, r_3, ..., r_N) -> (r_2 + bR, r_3, ..., r_N)`, is a surjective
  homomorphism of right modules. Its kernel is `{(r_1, r_2, 0, ..., 0) : r_2 in bR} = e_1 R + L_b`.

**Item 2.** For `g in GL_N(R)`, `g` maps `L + L'` onto `gL + gL'`, so it induces an isomorphism
`R^N/(L + L') -> R^N/(gL + gL')`. The class depends only on the unordered pair. Distinct orbits of pairs are then
separated by the classes of item 1. A subgroup of `GL_N(R)` has at least as many orbits as `GL_N(R)`.

**Item 3.**
- `R = eR ⊕ (1-e)R` as right modules, so `R/(1-e)R ≅ eR`, and `b = 1 - e != 0` since `e != 1`.
- Isomorphic modules have equal classes in `K_0(R)`, and `[eR ⊕ R^(N-2)] = [e] + (N-2)[1]`. So distinct classes
  `[e]` give non-isomorphic quotients, hence distinct orbits of pairs, all inside `Ω_N^0 ⊆ Ω_N(R)`.

**Item 4.**
- In `M_n(R_n)` the diagonal matrix units `f_1, ..., f_n` are orthogonal idempotents summing to `1`, with
  `f_i R ≅ f_1 R`. So `n[f_1] = [1]`. Write `f_n` for this `f_1`.
- Suppose `[f_n] = [f_m]`. Then `(n - m)[f_n] = [1] - [1] = 0`, so `(n - m)[1] = n(n - m)[f_n] = 0`. Since `[1]` has
  infinite order, `n = m`.
- If `U_Q ⊆ R` unitally, then `M_(n!)(Q) ⊆ R` unitally, and its matrix units give `R ≅ M_(n!)(R')` with
  `R' = f_11 R f_11`.
- `PE_N(R)` (gq-referee-a, N1). An element `g` of `Z(E_N(R))` commutes with every `e_ij(r)`, hence with every
  matrix unit `E_ij`, so `g = cI` with `c in Z(R)^x`. Then `cI · vR = v c R = vR`. So `Z(E_N(R))` fixes every line,
  and `PE_N(R)` acts on `Ω_N(R)` with the same orbits as `E_N(R)`.
