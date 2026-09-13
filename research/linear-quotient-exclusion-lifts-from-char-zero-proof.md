---
rg: 2
id: linear-quotient-exclusion-lifts-from-char-zero-proof
kind: route
title: Clear denominators in a rational Nullstellensatz certificate; spread a number-field point to almost all primes
target: linear-quotient-exclusion-lifts-from-char-zero
requires: [simple-vertex-groups-vtf-iff-some-finite-quotient]
---

Let `Λ = <s_1, ..., s_m | r_1, ..., r_l>`, and let `w` be a word representing `x`.

**The systems.** The variables are:
- the entries of `d × d` matrices `X_1, ..., X_m`;
- scalars `u_1, ..., u_m` with `u_i det(X_i) = 1`, so `X_i^{-1} = u_i adj(X_i)`;
- scalars `λ_1, ..., λ_l, μ_1, ..., μ_l` with `λ_j μ_j = 1`;
- one scalar `t`.

The common equations are `u_i det X_i = 1`, `λ_j μ_j = 1` and `r_j(X) = λ_j I`, where
`r_j(X)` is evaluated with the adjugate inverses.

Put `W = w(X)`. The system `S_i` adds one equation saying that a chosen linear coordinate
`c_i(W)` is invertible, `t c_i(W) = 1`. Here `c_i` runs over the `d^2 - 1` functionals
`W_ab` for `a != b` and `W_aa - W_11` for `a >= 2`; they all vanish exactly on scalar
matrices. All coefficients are integers.

**Solutions are representations.** Let `k` be a field.
- A homomorphism `ρ : Λ -> PGL_d(k)` with `ρ(x) != 1` gives `k`-points: choose lifts
  `X_i in GL_d(k)` of the `ρ(s_i)`. Each relator evaluates to a scalar, and `W` is not
  scalar, so some `c_i(W) != 0`.
- Conversely, a `k`-point of some `S_i` defines such a `ρ`.
So `H_d(k) != ∅` iff some `S_i` has a `k`-point. The same holds with `k-bar`, and
`H_d(k) ⊆ H_d(k-bar)`.

**(L1)(b) and (L2).** Suppose `H_d(C) = ∅`.
- Then no `S_i` has a point over `Q-bar ⊂ C`. By Hilbert's Nullstellensatz over `Q`,
  `1` lies in the ideal of `S_i` in `Q[vars]`: `1 = Σ_j g_j h_j` with `g_j in Q[vars]`.
- Multiplying by a common denominator gives `N_i = Σ_j g'_j h_j` with `g'_j in Z[vars]`
  and `N_i >= 1`. Put `N = lcm_i N_i`.
- Take a field `k` with `char k` not dividing `N`, characteristic 0 included. Then `N_i`
  is a unit in `k`, so `1` lies in the ideal of `S_i` over `k`, and `S_i` has no
  `k-bar`-point. Hence `H_d(k) = ∅`.
- For a prime `p` dividing `N`, a reduced Groebner basis of `S_i` over `F_p` equals `{1}`
  iff `S_i` has no `F_p-bar`-point (Nullstellensatz over `F_p`). This decides the
  finitely many remaining characteristics.

**(L1)(a).** Suppose `H_d(C) != ∅`.
- Some `S_i` has a `C`-point, hence a `Q-bar`-point, by the Nullstellensatz: `1` is not in
  its ideal over `Q`, since a certificate would kill the `C`-point.
- Its coordinates lie in a number field `K`, and in `O_K[1/M]` for some integer `M`.
- Take a prime `p` not dividing `M`, and a prime `𝔭` of `O_K` over `p`. Reduction modulo
  `𝔭` gives an `F_p-bar`-point of the equations of `S_i`.
- The one extra equation `t c_i(W) = 1` survives reduction automatically, because `t` is
  among the coordinates. So every equation holds mod `𝔭`, and `H_d(F_p-bar) != ∅` for
  all `p` not dividing `M`.

**(L3).** A nontrivial homomorphism `Λ -> S` is injective on every vertex group, by the
Lemma of `simple-vertex-groups-vtf-iff-some-finite-quotient`. Composed with a faithful
projective representation `S -> PGL_d(F)`, it gives `ρ` with `ρ(x) != 1`, where `x != 1`
lies in a vertex group.
