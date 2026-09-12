---
rg: 2
id: non-mf-from-stable-osin-horn-separator
kind: route
title: A dimension-free modulus for one separator beats the torsion gap in the corona
target: osin-periodic-quotient-is-non-mf
requires:
  - osin-horn-separator-is-opnorm-stable
  - osin-torsion-universal-theory-separator
  - finite-order-unitary-has-uniform-opnorm-gap
---

Suppose `Gbar = G/G^n` were MF, so that there is an injective homomorphism

```text
Gbar  ->  U(Q),        Q = (prod_n M_(d_n)) / (oplus_n M_(d_n)),
```

and write `u_1,...,u_s` for the images of the generators `x_1,...,x_s`. Lift
them to unitary matrices `U_(i,n)` by the polar-decomposition argument of
`corona-restricted-burnside-equals-power-law-moduli-proof`, and recall
`||a|| = limsup_n ||A_n||` for a representative `(A_n)`.

**The hypotheses of `(OSM1)` are met eventually.**

* Each `R_i` is a relator of `G`, hence trivial in `Gbar`, so `R_i(u) = 1`
  in the corona and `||R_i(U_n) - I|| -> 0`.
* `Gbar` has exponent dividing `n`, so `v(u)^n = 1` for **every** word `v`,
  and in particular `||v_l(U_n)^n - I|| -> 0` for each of the finitely many
  `v_1,...,v_r` named by `osin-horn-separator-is-opnorm-stable`.

Because `t + r` is finite, one threshold `n_0` serves all of them, and for
`n >= n_0` both displayed hypotheses hold with the constant `eta` of
`(OSM1)`.

**The conclusion contradicts the gap.**  For `n >= n_0`, `(OSM1)` gives some
index `j(n)` with `||W_(j(n))(U_n) - I|| < delta_n/2`. Passing to a
subsequence on which `j(n)` is a constant `j` -- possible since `q` is finite
-- and taking the `limsup` along it,

```text
|| W_j(u) - 1 ||  <=  delta_n / 2.
```

But `W_j != 1` in `Gbar` by `(OS1)` and the embedding is injective, so
`W_j(u) != 1`; and `W_j(u)` lies in a group of exponent dividing `n`, so
`W_j(u)^n = 1`. `finite-order-unitary-has-uniform-opnorm-gap` then forces

```text
|| W_j(u) - 1 ||  >=  delta_n = 2 sin(pi/n),
```

contradicting the previous line. Hence no such embedding exists and `Gbar`
is not MF.

**Where each prerequisite is spent.**  `osin-torsion-universal-theory-separator`
supplies `(OS1)` -- that all `q` words survive in `Gbar` -- which is what
makes the disjunctive conclusion of `(OSM1)` fatal rather than merely
inconvenient; the subsequence step is the only place the disjunction costs
anything. `osin-horn-separator-is-opnorm-stable` supplies the modulus, and is
the sole open input. The gap claim supplies the lower bound, in the corona,
where it holds because it was stated for an arbitrary unital C*-algebra.
