---
rg: 2
id: laurent-right-ideals-of-cantor-crossed-products-columnwise-proof
kind: route
title: Laurent division has bounded support, and the quotient of a pattern-equivariant banded operator is again pattern-equivariant and banded
target: laurent-right-ideals-of-cantor-crossed-products-columnwise
requires: []
artifacts:
  - research/artifacts/sk-algebraic-putnam-2026-09-13-part1.md
---

Notation: `(fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}`. In the orbit representation `a = Σ_jf_ju^j` acts by `aδ_n = Σ_jf_j(T^{n+j}x)δ_{n+j}`, with entries `a(m,n) = f_{m−n}(T^mx)`. The representation is faithful, since the orbit of `x` is dense and the `f_j` are continuous.

**Only if.** `(qy)δ_t = q(yδ_t) ∈ qV`.

**If.**
1. **Normalize.** `q = u^αq_0` with `q_0 ∈ F[u]`, `q_0(0) ≠ 0`, `d = deg q_0`. As `u^α` is a unit, `qR = q_0R` and `qV = q_0V`. Let `z = Σ_jζ_ju^j` have propagation `w`, so `supp zδ_t ⊆ [t−w, t+w]`.
2. **Support.** If `v ∈ q_0V` is supported in `[m,M]`, write `v = u^mP` with `deg P ≤ M−m`. `q_0 | P` in `F[u]` because `q_0(0) ≠ 0`. So the quotient `v′` with `q_0v′ = v` is supported in `[m, M−d]`.
3. **Formula.** Let `q_0^{−1} = Σ_{i≥0}λ_iu^i` in `F[[u]]`. Back-substitution gives `(yδ_t)_m = Σ_{k=t−w}^{m}λ_{m−k}z(k,t)` for the quotient `yδ_t` of `zδ_t`. It is supported in `[t−w, t+w−d]`.
4. **Membership.** `z(k,t) = ζ_{k−t}(T^kx)`, so `y(m,t) = η_{m−t}(T^tx)` with `η_i(ξ) = Σ_{j=−w}^{i}λ_{i−j}ζ_j(T^jξ)` for `−w ≤ i ≤ w−d`. These are locally constant functions. The element `y := Σ_i(η_i∘T^{−i})u^i ∈ R` has entries `(η_{m−t}∘T^{−(m−t)})(T^mx) = η_{m−t}(T^tx)`, as required.
5. **Conclusion.** `q_0y = z` in the faithful representation, so `z = q_0y ∈ q_0R = qR`. ∎
