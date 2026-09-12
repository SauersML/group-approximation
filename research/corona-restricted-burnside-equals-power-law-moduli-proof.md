---
rg: 2
id: corona-restricted-burnside-equals-power-law-moduli-proof
kind: route
title: Unitary lifts one way, diagonalization over the countable free group the other
target: corona-restricted-burnside-equals-power-law-moduli
requires:
  - restricted-burnside-finiteness
---

# Preliminary: unitary lifting

Let `u in U(Q)`. Choose bounded matrix representatives `(X_n)`. Unitarity in
the quotient gives `||X_n^* X_n - I|| -> 0`, so `X_n` is invertible for all
large `n`; set

```text
U_n = X_n (X_n^* X_n)^(-1/2)
```

for those `n` and `U_n = I` for the finitely many others. Each `U_n` is
unitary and `||U_n - X_n|| -> 0`, so `(U_n)` represents the same class `u`.
Thus every unitary of `Q` has a lift by a sequence of unitary matrices; there
is no `K_1` obstruction to overcome, because the correction is the polar part
of an eventually invertible sequence.

For a word `w in F_m` and lifts `U_i = (U_(i,n))`, the class of
`(w(U_(1,n),...,U_(m,n)))_n` is `w(u_1,...,u_m)`, and for any `a in Q` with
representative `(A_n)`,

```text
|| a || = limsup_n || A_n ||.                                    (LIM)
```

# (B) implies (A)

Let `u_1,...,u_m in U(Q)` generate a subgroup of exponent dividing `N`, and
take unitary lifts `U_(i,n)` as above. Every element of the subgroup is
`w(u)` for some `w in F_m`, so `w(u)^N = 1` for **every** `w in F_m`, i.e.

```text
|| w(U_n)^N - I || -> 0        for each fixed w in F_m.          (ZERO)
```

Fix a relator `s_j` and `eps > 0`, and take `W, eta` from `(B)`. Because `W`
is **finite**, `(ZERO)` gives an `n_0` with
`max_(w in W) ||w(U_n)^N - I|| < eta` for all `n >= n_0`; the finiteness of
`W` is exactly what makes this a single threshold rather than a diagonal
argument. Hence `||s_j(U_n) - I|| < eps` for `n >= n_0`, and by `(LIM)`

```text
|| s_j(u) - 1 || <= eps.
```

As `eps > 0` was arbitrary, `s_j(u) = 1`. (Alternatively, by the sharpened
target it is enough to run this once with `eps < delta_N`.)

Doing this for `j = 1,...,k`, the assignment `x_i |-> u_i` kills every
relator of `(RB1)`, so `F_m -> <u_1,...,u_m>` factors through `R(m,N)`. By
`restricted-burnside-finiteness` that group is finite, so the corona subgroup
is finite. This is `(A)`.

# (A) implies (B)

Contrapositive. Suppose `(B)` fails for some relator `s = s_j`: there is
`eps_0 > 0` such that for **every** finite `W subset F_m` and every
`eta > 0` some dimension and some tuple defeat the implication.

Enumerate `F_m = {w_1, w_2, ...}` (it is countable). For each `n >= 1` apply
the failure with

```text
W_n = {w_1,...,w_n},        eta_n = 1/n,
```

obtaining a dimension `d_n` and a tuple `U_n = (U_(1,n),...,U_(m,n)) in U(d_n)^m`
with

```text
max_(1 <= r <= n) || w_r(U_n)^N - I || < 1/n,                    (D1)
|| s(U_n) - I || >= eps_0.                                       (D2)
```

Form the corona `Q` for the sequence `(d_n)` and put `u_i = [(U_(i,n))_n]`.

Fix `r`. For all `n >= r`, `(D1)` gives `||w_r(U_n)^N - I|| < 1/n -> 0`, so
by `(LIM)` `w_r(u)^N = 1`. Since `r` was arbitrary, **every** element of
`<u_1,...,u_m>` has order dividing `N`: the subgroup has exponent dividing
`N`. This is where the diagonal enumeration is spent -- each fixed word is
tested from some point on, which is all `(LIM)` needs.

Meanwhile `(D2)` and `(LIM)` give

```text
|| s(u) - 1 || = limsup_n || s(U_n) - I || >= eps_0 > 0,
```

so `s(u) != 1`. But `s in ker(F_m -> R(m,N))`, so if `<u_1,...,u_m>` were
finite it would be a finite `m`-generated group of exponent dividing `N`,
hence a quotient of `R(m,N)` by `restricted-burnside-finiteness`, and `s(u)`
would be `1`. Therefore the subgroup is infinite, contradicting `(A)`.

This proves `(A) => (B)`, and with it the equivalence. Note the failure
direction is constructive: the tuple `(u_i)` above *is* the witnessing
exponent-`N` corona subgroup escaping `R(m,N)`, which is the fork recorded in
the claim.
