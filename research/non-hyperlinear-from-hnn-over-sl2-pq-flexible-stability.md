---
rg: 2
id: non-hyperlinear-from-hnn-over-sl2-pq-flexible-stability
kind: route
title: Centralize SL2(Z[1/p]) inside a flexibly stable SL2(Z[1/pq]) by a new letter
target: non-hyperlinear-group
requires:
  - sl2-z-inverse-pq-is-flexibly-hs-stable
  - sl2-s-arithmetic-pair-is-codense-kazhdan
  - hnn-over-codense-kazhdan-subgroup-not-hyperlinear
---

*Not a duplicate of `non-hyperlinear-from-hnn-over-codense-kazhdan`.*  That
route consumes `stable-group-with-codense-kazhdan-subgroup`, whose statement
asks for same-dimension stability.  Its only `SL_2(Z[1/pq])` host route
consumes the refuted strict claim.  This route names the flexible hypothesis
explicitly and consumes the HNN Corollary exactly as stated.

Take `A = SL_2(Z[1/pq])`, `C = SL_2(Z[1/p])` and `a_1 = diag(q, q^(-1))`,
which is not in `C`.  By `sl2-s-arithmetic-pair-is-codense-kazhdan`, `C` is
finitely generated with (T;FD).  This gives the uniform conjugation gap for
`Ad rho|_C` over all finite-dimensional unitary `rho` of `A`: `Ad rho|_C` is
a finite-dimensional representation of `C`, and its invariant vectors are
`rho(C)'`.  The pair is also finite-dimensionally co-dense.  These are the
Data of `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`.

Its Corollary, under flexible HS-stability of `A`
(`sl2-z-inverse-pq-is-flexibly-hs-stable`), gives that

```text
G_(p,q) = < SL_2(Z[1/pq]), t | [t, c] = 1 (c in S_C) >
```

is not hyperlinear.  It is finitely presented because `A` is finitely
presented and `S_C` is finite, so it is an explicit non-hyperlinear group.

The route does not use the strict notion anywhere, so
`sl2-z-inverse-pq-is-not-strictly-hs-stable` does not touch it.
