---
rg: 2
id: stw99-xcix-common-ultraproduct-proof
kind: route
title: Match bounded coordinate sequences with an ultranorm-null error
target: stw99-xcix-vanishing-kk-distance-identifies-ultraproducts
requires: []
---

Put `gamma_n=d_KK(A_n,B_n)`.  Let `(a_n)` be a bounded sequence with
`a_n in A_n`.  For `a_n!=0`, apply the Hausdorff estimate to
`a_n/||a_n||` and choose `b_n in B_n` with

```text
||b_n|| <= ||a_n||,
||a_n-b_n|| <= (gamma_n+1/n)||a_n||.
```

Take `b_n=0` when `a_n=0`.  The sequence `(b_n)` is bounded and
`lim_omega ||a_n-b_n||=0`, so `(a_n)` and `(b_n)` define the same element of
`prod_omega C_n`.  This proves one inclusion.  The Kadison--Kastler distance
is symmetric, so the same argument with `A_n,B_n` interchanged proves the
reverse inclusion.
