---
rg: 2
id: bs14-energy-threshold-active-passive-ledger
kind: claim
title: Cubic energy gives an e-half active padding ledger and an e-eighth passive cost
distinct_from:
  scalar-bs14-exit-angle-energy-dichotomy: that proves the one-direction inequality and phase fence; this chooses the global threshold and records normalized padding and displacement rates.
  bs14-flexible-cross-packet-boundary-reconciliation: that must construct the dilation from a near-solution; this is the exact ledger once positive-corner singular directions have been identified.
  two-cubic-residual-carriers-recover-the-deleted-source: that uses a transverse angle to identify source directions; this remains valid even on parallel modes by paying their active rank.
---

In the rank-`k` positive-corner setup of
`positive-fixed-corner-cubic-energy-charges-deleted-rank`, let `d=dim(PH)`,
let

```text
E=||(X_0S_0^2)^3-1||_F^2,
e=E/d,                                                (ATL1)
```

and let `a_j` be the eigenvalues of `QXQ`.  For `0<e<1`, choose

```text
tau=e^(1/4).                                          (ATL2)
```

Call a direction active when `1-a_j^2>=tau`.  Then

```text
rank(Q_active)/d <= (8/3)e^(1/2).                     (ATL3)
```

On the passive complement, the off-diagonal source coupling satisfies

```text
||P X Q_passive||_(2,d)^2<=tau,
||P X Q_passive||_(2,d)<=e^(1/8).                     (ATL4)
```

Thus all near-parallel passive directions can be deleted at normalized-HS
cost `O(e^(1/8))`, while every active direction may be paid for by flexible
padding of relative size `O(e^(1/2))`.  Taking the union of both cubic
high-residual carriers or overpadding source and exit separately changes
only the universal constant in `(ATL3)`.

This estimate is phase-uniform and block-free inside an exposed positive
corner.  It does not identify that corner from the compressed tuple.  A
reverse polar/Gram construction with the same ledger would already prove
the qualitative flexible endpoint, although not the sharper quadratic
padding target `k=O(E)`.

