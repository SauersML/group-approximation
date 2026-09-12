---
rg: 2
id: literal-integer-crossed-product-qd-destruction-proof
kind: route
title: Use the locally RF telescope core and the literal nonquasidiagonal canonical trace
target: integer-crossed-products-can-destroy-quasidiagonal-traces
requires:
  - amenable-crossed-products-preserve-invariant-amenable-traces
  - locally-rf-groups-have-quasidiagonal-canonical-trace
  - literal-telescope-core-lef
  - literal-telescope-split-normal-form
  - literal-canonical-trace-hyperlinear-not-quasidiagonal
artifacts:
  - research/artifacts/amenable-crossed-product-trace-dichotomy-2026-08-30.md
---

Let `K=E_T=ker(E->Z)`.  The split normal form gives
`E=K rtimes_alpha Z` and therefore

```text
C*_(max)(E)=C*_(max)(K) rtimes_(alpha,max) Z.              (1)
```

Every finitely generated subgroup of `K` is residually finite by
`literal-telescope-core-lef`.  Hence
`locally-rf-groups-have-quasidiagonal-canonical-trace` makes the canonical
trace `tau_K` on `C*_(max)(K)` quasidiagonal.  It is invariant under
`alpha`, since every group automorphism preserves the identity coefficient.
Quasidiagonal trace models are amenable trace models because normalized
Hilbert--Schmidt norm is bounded by operator norm.

Apply `amenable-crossed-products-preserve-invariant-amenable-traces` to
`Q=Z`.  The induced trace `tau_K compose E` on the right side of (1) is
amenable.  Under (1) it is exactly the canonical trace `tau_E`.
But `literal-canonical-trace-hyperlinear-not-quasidiagonal` proves that
`tau_E` is not quasidiagonal.  This supplies all clauses of the target.

There is no contradiction with finite crossed-product permanence: the
Folner compression has small normalized-rank boundary but its operator norm
need not decay.  That boundary is exactly where amenability survives and
quasidiagonality fails.
