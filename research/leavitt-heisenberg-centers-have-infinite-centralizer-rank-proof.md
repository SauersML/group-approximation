---
rg: 2
id: leavitt-heisenberg-centers-have-infinite-centralizer-rank-proof
kind: route
title: Determinants over F_2(c) forbid ab = cba in finite dimension, the quantum torus is simple, and Frobenius-type index counting forbids x ~ x^k
target: leavitt-heisenberg-centers-have-infinite-centralizer-rank
requires: []
artifacts: [research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md]
---

The full proofs are Propositions 5 and 6 of `research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md`.

1. **(i)** `a` and `b` are units of `A = F_2(c) ⊗ C_c`, in which `c` is central. If `n = dim_(F_2(c)) A` were
   finite, then `L_a L_b = c L_b L_a` on `A` would give `c^n = 1` by determinants, which is impossible for
   transcendental `c`.
2. **(ii)**
   - The localization of `F_2[H_3(Z)]` at its center `F_2[z] - {0}` is the quantum torus over `F_2(z)` with
     parameter `z`.
   - It is simple: a nonzero element of an ideal with fewest monomials is a monomial, because conjugation by
     `x` and by `y` rescales the monomials `x^i y^j` by `z^j` and `z^(-i)`.
   - So the induced map to `F_2(c) ⊗ C_c` is injective. `F_2[H_3(Z)]` is free over `F_2[z^(+-1)]`, so
     `F_2[H_3(Z)] -> R` is injective.
3. **(iii)**
   - Conjugation by `t` gives `rho(x) = dim_K K ⊗ C_(x^k)` with `K = F_2(x^(|k|))`.
   - `C_x <= C_(x^k)`, and localizing at `F_2[x^(|k|)] - {0}` inverts all nonzero `p(x)`, because each divides
     its norm. So `dim_K K ⊗ C_x = |k| rho(x) <= rho(x)`.
   - Since `rho(x) >= 1`, this forces `rho(x) = ∞`. ∎
