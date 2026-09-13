---
rg: 2
id: frobenius-bounded-corona-stable-finiteness-proof
kind: route
title: Weyl inequalities make the bounded-rank sequences an ideal, and polar decomposition makes the quotient finite
target: frobenius-bounded-corona-is-stably-finite
requires: []
---

Notation as in the target.

**(1) Ideal.**  Weyl's inequalities for singular values give
`s_(i+j-1)(X+Y) <= s_i(X) + s_j(Y)`, `s_i(AXB) <= ||A|| s_i(X) ||B||` and
`s_i(X) <= s_i(Y) + ||X - Y||`.  Hence

```text
rank_(>t)(X+Y) <= rank_(>t/2)(X) + rank_(>t/2)(Y),
rank_(>t)(AXB) <= rank_(>t/(||A|| ||B||))(X),
rank_(>t)(X)   <= rank_(>t/2)(Y)        whenever ||X - Y|| < t/2 .
```

The first two show that `K` is a two-sided ideal, `X^*` has the singular
values of `X`, and the third shows `K` is closed in the sup norm.  If
`||X_L|| -> 0`, then for each `t > 0` only finitely many `L` have
`rank_(>t)(X_L) > 0`, so `(X_L) in K`.  If `(X_L) in K` with
`M = sup ||X_L||` and `r = sup_L rank_(>t)(X_L)`, then

```text
||X_L||_(2,k_L)^2 = (1/k_L) sum_i s_i(X_L)^2 <= (r M^2 + k_L t^2) / k_L ,
```

so `limsup_L ||X_L||_(2,k_L) <= t` for every `t > 0`.

**(2) Stable finiteness.**  Let `v in Q` with `v^* v = 1` and let `(X_L)` be a
bounded lift, so `X^* X - 1 in K`.  In each finite dimension take the polar
decomposition `X_L = W_L |X_L|` with `W_L` unitary.  Since
`(|X| + 1)^(-1)` has norm at most `1`,

```text
|X| - 1 = (|X|^2 - 1)(|X| + 1)^(-1) in K,       X - W = W (|X| - 1) in K,
```

so `v = [W_L]` is unitary and `v v^* = 1`.  Thus `Q` is finite.  For `m >= 1`,
`M_m(Q)` is the same construction for the sizes `m k_L`: an `m x m` matrix of
sequences in `K` is a sum of `m^2` terms `e_(ab) ⊗ X^(ab)`, each with the
singular values of `X^(ab)`, so by the Weyl sum inequality it lies in the
size-`m k_L` ideal; conversely every entry of an element of that ideal is a
compression of it and lies in `K`.  The finiteness argument used only finite
dimensionality and the ideal property, so every `M_m(Q)` is finite.

**(3) Models.**  Put `D_L(g,h) = V_L(gh) - V_L(g) V_L(h)` with
`||D_L(g,h)||_F <= C`.  Then `rank_(>t)(D_L) <= C^2 / t^2`, so
`(D_L(g,h)) in K`.  With `g = h = 1`, `1 - V(1) = V(1)^* (V(1) - V(1)^2) in K`;
with `h = g^(-1)`, `V(g^(-1)) = V(g)^*` modulo `K`.  So `[V_L(g)]` is a
homomorphism into `U(Q)`.  For a tracial state `tau = lim_omega tr_(k_L)`,
`|tr_k(X)| <= ||X||_(2,k)`, which tends to `0` on `K` by (1).

**(4) Stable finiteness is not an obstruction.**  The left regular
representation `lambda : G -> U(C*_r(G))` is injective.  The canonical trace
`tau` of `C*_r(G)` is faithful, so `tr_m ⊗ tau` is faithful on
`M_m(C*_r(G))`; an isometry `v` there has
`(tr_m ⊗ tau)(1 - v v^*) = (tr_m ⊗ tau)(v^* v - v v^*) = 0`, so `v v^* = 1`.
