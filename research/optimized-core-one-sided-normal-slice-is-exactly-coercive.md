---
rg: 2
id: optimized-core-one-sided-normal-slice-is-exactly-coercive
kind: claim
title: The complete one-sided exact-core normal slice has an exact nonlinear coercivity identity
distinct_from:
  uniform-gauge-optimized-induced-energy: that asks for a global estimate over every exact supplied core and every involution; this proves it with constant two on the full nonlinear slice obtained by multiplying one exact implementer by an arbitrary unitary in the root commutant.
  optimized-core-absorbs-endpoint-conjugations: that moves the endpoint and both core generators by a common conjugation; this keeps the endpoint and root generator fixed and moves only the BS implementer, so it is transverse to that conjugation orbit.
  same-core-involution-cubic-gauge-coercivity: that compares two extending unitaries over one fixed core; this compares two exact cores under one fixed extending involution.
---

Let `(X,R,T)` be any exact level-`N` square-free endpoint and let `q` be
an arbitrary unitary in `{T}'`.  Put

```text
R_q=qR,                    b_q=(R_q,T),               (ONS1)
u=(X R_q)^2,               v=(X T^2 R_q)^3.          (ONS2)
```

Then `b_q` is an exact level-`N` BS core and the following finite-difference
identity holds:

```text
||q-1||_2=||v-u||_2.                                  (ONS3)
```

Consequently

```text
||q-1||_2 <= ||u-1||_2+||v-1||_2,                    (ONS4)
G_N(X,b_q) <= 2 E_end(X,b_q).                         (ONS5)
```

The statement is global and dimension-free.  In particular `q` may be
operator-far from `1`, supported on an arbitrarily small-rank carrier, and
may move through different spectral multiplicities.  Thus none of those
mechanisms can refute the optimized target while the supplied core remains
in this complete one-sided root-commutant slice.

Equivalently, suppose `(X,T)` admits at least one exact completion
`(X,R_0,T)`.  Then **every** exact level-`N` BS core `(R_1,T)` over the same
root satisfies

```text
G_N(X,(R_1,T)) <= 2 E_end(X,(R_1,T)).                 (ONS6)
```

Indeed `R_1=qR_0` for a unitary `q in {T}'`, so this is exactly `(ONS5)`.
Hence the open optimized estimate has no remaining wrong-implementer
obstruction over an authenticated first modular vertex.  Its surviving
content starts before `(X,T)` has been selected inside an extendible exact
vertex type.

## Interpretation

The slice in `(ONS1)` includes all exact core changes which keep `T` fixed:
the BS relation only requires `[q,T]=1`; no commutation with `R` is assumed.
Conversely, if `R_0` and `R_1` both implement `T -> T^4`, then
`q=R_1R_0^(-1)` commutes with `T^4`, and therefore with `T` because
`gcd(4,N)=1`.  Thus no exact implementers over this root lie outside the
slice.
The competitor `(R,T)` in the definition of `G_N` restores an exact endpoint,
and `(ONS3)` says that its full core-motion cost is already visible in the
difference of the inversion and second-cubic row values.  This is not a
Taylor or coordinate-basin estimate: there is no remainder and no
smallness hypothesis.
