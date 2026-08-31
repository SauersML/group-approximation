---
rg: 2
id: stw99-x2-local-afd-at-partial-trace-rate
kind: claim
title: Partial-trace spectral cuts prove local AFD at inverse matrix-dimension rate
distinct_from:
  x2-local-afd-holds-at-rate-controlled-packets: that result cuts every matrix entry separately and requires a d^{-5/2} approximation rate; this result uses one operator-valued partial trace and improves the sufficient rate to d^{-1}.
  shadow-avoidance-fails-at-column-isometries: that counterexample has two-norm size d^{-1/2}, so it lies outside the d^{-1} positive cell and does not refute it.
artifacts:
  - research/artifacts/stw99-x2-2026-literature-and-route-audit-2026-08-31.md
---

Let `Y = {y_1,...,y_j} subset R`, and let `M = M_d subset R` be a
unital matrix subfactor.  Write
`R = M_d bar-tensor N`, where `N = M' cap R`.  If

```text
dist_2(y_i, M) <= delta <= epsilon / (2 sqrt(j) d),   i=1,...,j,
```

then there is a projection `0 != s in N` and the finite-dimensional
algebra `B = M_d tensor C s`, with support `s`, such that

```text
||[y_i,s]|| <= 2 epsilon,
||s y_i s - E_B(s y_i s)|| <= 2 epsilon,   i=1,...,j.
```

Thus Popa's local-AFD criterion holds for every packet whose
finite-dimensional two-norm approximation rate is `O(d^{-1})`.  This
strictly improves the previously recorded entrywise rate `O(d^{-5/2})`.
It does not settle STW Problem X(2): hyperfiniteness gives no rate relating
`dist_2(Y,M_d)` to `d`, and the column-isometry obstruction occurs at the
larger scale `d^{-1/2}`.

The factor `d` in the block inequality used by the proof is sharp:
inside `M_d tensor M_d subset M_d tensor N`, the unnormalised maximally
entangled rank-one operator `X=|Omega><Omega|`,
`Omega=sum_a e_a tensor e_a`, has `sum_a X_aa=1` and `||X||=d`.
Thus this exact partial-trace argument cannot improve its `d^{-1}` rate.
