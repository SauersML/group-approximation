---
rg: 2
id: codense-tau-coset-outlier-proof
kind: route
title: Project the base-coset chart label through the exact finite-action tau gap
target: codense-tau-coset-soficity-forces-permutation-instability
requires: []
---

Fix `h in A\C`.  Suppose that a sofic orbit approximation to `A action A/C`
has state set `V`, approximately multiplicative map `phi:A->Sym(V)`, good
set `V_0`, and injective charts `pi_v:E->B`, where

```text
{C,h^(-1)C} subset E
```

and the covariance equations are imposed for `S_C union {h}`.  Suppose also,
towards correction, that after padding by `o(|V|)` points there is an exact
finite action `rho:A->Sym(V')` with `phi(g)` Hamming-close to `rho(g)` on
this finite set.  Discarding the padding and all endpoints at which the two
maps differ changes the estimates only by `o(1)`.  We therefore write
`epsilon` for one quantity dominating the atlas error, correction error, and
padding proportion.

For `v in V_0`, put

```text
ell(v)=delta_(pi_v(C)) in l2(B),
```

and extend `ell` by arbitrary unit vectors off `V_0`.  Regard `ell` as a
unit vector in the normalized space `l2(V';l2(B))`.  For `c in S_C`, orbit
covariance gives

```text
pi_(phi(c)v)(C)=pi_v(c^(-1)C)=pi_v(C)
```

whenever both chart endpoints are good.  Hence

```text
||rho(c)ell-ell||_2^2 = O(epsilon)                                (CTP1)
```

uniformly on `S_C`.  The assumed tau gap applies to `l2(V')`; tensoring with
the trivial coefficient space `l2(B)` does not change it.  If `P_C` denotes
projection onto the `rho(C)`-invariant vectors, then

```text
||ell-P_C ell||_2^2 = O(epsilon/kappa^2).                          (CTP2)
```

By `(CTS1)`, `rho(C)` and `rho(A)` are the same permutation subgroup, so
`P_C ell` is `rho(h)`-invariant.  It follows that

```text
||rho(h)ell-ell||_2^2 = O(epsilon/kappa^2).                        (CTP3)
```

On the other hand, covariance for `h` gives

```text
ell(phi(h)v)=delta_(pi_v(h^(-1)C)).                                (CTP4)
```

The chart is injective and `h^(-1)C != C`, so the two one-hot vectors in
`(CTP4)` and the definition of `ell(v)` are orthogonal at every good pair of
endpoints.  Thus

```text
||phi(h)ell-ell||_2^2 >= 2(1-O(epsilon)).                          (CTP5)
```

Closeness of `phi(h)` to `rho(h)` changes the squared norm by only
`O(epsilon)`.  Equations `(CTP3)` and `(CTP5)` contradict each other as
`epsilon->0`.  Therefore the action's sofic approximations cannot be
flexibly corrected to exact finite actions, proving the claim.

For `A=PSL_2(Z[1/2])` and `C=PSL_2(Z)`, `(CTS1)` is congruence co-density.
Selberg's property `(tau)` gives the uniform gap on every congruence quotient;
because every finite action of `A` factors through such a quotient and an
arbitrary quotient action is a subrepresentation of copies of its regular
representation, it gives exactly the gap assumed above.

