---
rg: 2
id: unit-roots-divide-centralizer-rank-proof
kind: route
title: A k-th root makes the localized centralizer a vector space over the degree-k field K(x^(1/k)), by Eisenstein at x
target: unit-roots-divide-centralizer-rank
requires: []
---

Notation as in `unit-roots-divide-centralizer-rank`. Put `M = K(x) ⊗_(K[x]) C_x`, the localization of the
left `K[x]`-module `C_x` at `K[x] − {0}`.

1. **`M ≠ 0`.** The kernel of `C_x -> M` is the `K[x]`-torsion of `C_x`. The element `1` is not torsion,
   since `p(x)·1 = p(x) ≠ 0` for every nonzero `p` (transcendence). So the image of `1` is nonzero.
2. **`y` is transcendental.** If `P(y) = 0` for a nonzero `P in K[s]`, then `x = y^k` would be algebraic,
   because `K[y]` would be a finite-dimensional `K`-algebra containing `x`. So `y` is transcendental over `K`.
3. **A module over a field of degree `k`.** `y` commutes with `x = y^k`, so `y in C_x`, and left
   multiplication by `y` is a `K[x]`-linear endomorphism of `C_x` (it commutes with left multiplication by `x`).
   It therefore acts on `M`, and it satisfies `y^k = x` there. So `M` is a module over
   `E = K(x)[s]/(s^k − x)`.
4. **`E` is a field of degree `k` over `K(x)`.** The polynomial `s^k − x` is Eisenstein at the prime `x` of the
   UFD `K[x]`, hence irreducible over `K(x)` by Gauss's lemma. This holds in every characteristic.
5. **Conclusion.** `M` is a nonzero `E`-vector space, so `dim_(K(x)) M = k · dim_E M`. Hence `rho(x)` is a
   multiple of `k` when finite, and `rho(x) >= k` in all cases. This is part 1.
6. **Part 2.** If `k`-th roots exist for infinitely many `k`, then `rho(x) >= k` for arbitrarily large `k`.
7. **Part 3.** Over `F_q`, an algebraic unit `x` lies in the finite ring `F_q[x]`. Left multiplication by `x`
   is injective on it (x is a unit of `R`), hence bijective, so `x` is a unit of the finite ring `F_q[x]` and
   has finite order. So an infinite-order unit is transcendental, and parts 1–2 apply. A torsion-free element
   with roots of unbounded order has infinite order. ∎
