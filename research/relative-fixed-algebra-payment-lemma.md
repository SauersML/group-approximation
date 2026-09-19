---
rg: 2
id: relative-fixed-algebra-payment-lemma
kind: claim
title: An adjoint expander charges a carrier exactly to the extent it avoids the full fixed algebra
distinct_from:
  finite-group-intertwiner-laplacian-gap: that supplies the multiplicity-independent spectral gap but leaves the full intertwiner algebra as kernel; this identifies the additional no-capture datum needed to make a projection pay energy.
  marked-hs-separation-forces-spectral-density: that supplies positive carrier trace beta; positive density alone does not keep the carrier out of a multiplicity commutant.
---

Let `S` be a finite unitary family in `M_d`, let `N={S}'`, and let `E_N` be
the trace-preserving conditional expectation. Assume the adjoint Poincare
gap

```text
sum_(s in S)||[s,x]||_2^2 >= kappa ||x-E_N(x)||_2^2.    (RFA1)
```

For every projection `p`,

```text
||p-E_N(p)||_2^2=tau(p)-||E_N(p)||_2^2.                 (RFA2)
```

Consequently, if

```text
tau(p)>=beta,
||E_N(p)||_2^2 <= (1-gamma)tau(p),                      (RFA3)
```

then

```text
sum_(s in S)||[s,p]||_2^2 >= kappa gamma beta.          (RFA4)
```

If the compiler also proves a dimension-independent covariance bridge

```text
sum_(s in S)||[s,p]||_2^2
 <= C sum_(r in R)||r(U)-I||_2^2,                       (RFA5)
```

then the defining relators pay the global floor `kappa gamma beta/C`.

For a finite group packet `rho:H->U(d)`, the no-capture condition has the
finite word form

```text
|H|^(-1) sum_(h in H) tau(p rho(h)p rho(h)^*)
 <= (1-gamma)tau(p).                                   (RFA6)
```

Thus error spreading has a precise surviving target: a marked carrier of
positive density must avoid the **full joint relative commutant**, and the
resulting covariance energy must be charged to boundedly many defining
relators.
