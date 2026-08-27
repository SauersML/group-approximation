---
rg: 2
id: finite-holonomy-crossed-product-ce-proof
kind: route
title: Embed the finite crossed product by its regular covariant representation
target: finite-holonomy-crossed-products-do-not-promote-canonical-trace
requires:
  - nonce-factor-in-group-factor-corner-forces-nonhyperlinear
---

First take an untwisted action.  On `M tensor B(l2(K))`, define

```text
rho(x)=sum_(g in K) alpha_(g^-1)(x) tensor e_(g,g),
rho(u_h)=1 tensor lambda_K(h).                                  (FHCP1)
```

These operators satisfy

```text
rho(u_h)rho(x)rho(u_h)^*=rho(alpha_h(x)),
```

so they give the regular covariant representation of `N`.  It is faithful
and normal.  The normalized tensor trace satisfies

```text
(tau tensor tr_K)(rho(x))=tau(x),
(tau tensor tr_K)(rho(xu_h))=0                    (h!=1),          (FHCP2)
```

which is exactly the canonical crossed-product trace.

For a cocycle action, insert the usual cocycle multipliers from `M` into the
off-diagonal entries of `rho(u_h)`.  They are unitary and do not change the
zero diagonal trace for `h!=1`; the same faithful regular representation and
trace calculation hold.

If `M` is CE, then `M tensor M_(|K|)` is CE and `(FHCP1)` makes `N` CE.  If
`N` is CE, restriction makes `M` CE.  Finally, any trace-preserving embedding
of `N` in a group-factor corner restricts to one of `M`, giving the stated
promotion reduction.

