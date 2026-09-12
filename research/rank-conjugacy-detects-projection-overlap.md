---
rg: 2
id: rank-conjugacy-detects-projection-overlap
kind: claim
title: Two-copy rank conjugacy detects projection overlap exactly and quantitatively
artifacts:
  - research/artifacts/independent-set-rounding-rank-router-2026-08-23.md
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that reads overlap through an authenticated partial-isometry source; this uses only trace preservation under unitary conjugacy and has an exact converse at zero overlap.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that obstructs a universally selected nonlinear predicate sector; this pays NAND by finite-dimensional rank conservation and leaves only affine block routing.
---

**ESTABLISHED.**  Let `P,Q` be projections in a finite tracial von Neumann
algebra, set

```text
A=1-2P,       B=1-2Q,
R=diag(A,B),  S=diag(AB,1),
```

and use the normalized trace on the two-copy amplification.  For every
unitary `U`,

```text
2||PQ||_2^2<=||URU^*-S||_2.                           (RCD1)
```

Conversely,

```text
PQ=0  =>  exists U with URU^*=S.                      (RCD2)
```

For finitely many forbidden pairs with weights `alpha_f`, `sum alpha_f<=1`,
and word defects

```text
e_f=||U_fR_fU_f^*S_f^*-1||_2^2,
delta=sum_f alpha_f||P_fQ_f||_2^2,
```

one has

```text
sum_f alpha_f e_f>=4delta^2.                          (RCD3)
```

There is no multiplicity, rank, alphabet-size, or dimension loss.

