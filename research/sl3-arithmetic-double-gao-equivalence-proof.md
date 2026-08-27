---
rg: 2
id: sl3-arithmetic-double-gao-equivalence-proof
kind: route
title: Use the dyadic diagonal as Gao's relative Haar unitary
target: sl3-arithmetic-double-hyperlinear-iff-relative-embeddable
requires: []
artifacts:
  - research/artifacts/gao-relative-embeddability-appendix-sl3-audit-2026-08-21.md
---

Gao's Theorem 7.1 says that for finite von Neumann algebras `N subset M`
and a finite factor `N_1`, `RE/N_1` implies

```text
M *_N M embeds into (R tensor N_1)^omega.                     (GEP1)
```

The converse from the PLAIN double holds if there is `u in U(M)` with
`E_N(u^n)=0` for every nonzero integer `n`.

Here `C=SL_3(Z)` is ICC: a finite conjugacy class would give a finite-index
centralizer, whose Zariski-dense subgroup forces the element to be scalar;
the center of `SL_3(Z)` is trivial.  Hence `N=L(C)` is a finite factor.  It
is Connes embeddable because `C` is residually finite, hence hyperlinear.

Take

```text
h=diag(2,1,1/2) in A,       u=lambda_A(h) in L(A).
```

For every `n!=0`, `h^n` has a nonintegral diagonal entry, so `h^n notin C`.
The group-factor conditional expectation therefore gives

```text
E_(L(C))(u^n)=0.                                               (GEP2)
```

Thus Gao's plain-double converse applies with `N_1=N`.  If `L(D)` is CE,
its embedding in `R^omega` followed by `x |-> x tensor 1` is an embedding in
`(R tensor N)^omega`, so Theorem 7.1 gives `RE/N`.  Conversely `RE/N` gives
`(GEP1)`; since `N` is CE, `R tensor N` is CE, and hence `L(D)` is CE.
Finally, canonical group hyperlinearity is equivalent to CE of `L(D)`.
