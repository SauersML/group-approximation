---
rg: 2
id: sl3-arithmetic-double-near-exact-fold-proof
kind: route
title: Feed the near-intertwining block swap into the exact projective co-density gap
target: sl3-arithmetic-double-near-exact-vertices-fold-projectively
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Put `rho_n=alpha_(n,0) direct_sum alpha_(n,1)` and let `V_n` be the
block-swap.  The amalgamating relators say that the two approximate vertex
images agree on each generator of `C`.  Telescoping `(ANV1)` along the fixed
words for those generators therefore gives

```text
max_(c in S_C) ||[V_n,rho_n(c)]-I||_2 = O(delta_n+epsilon_n). (ANP1)
```

The representations `rho_n` are exact.  Apply
`exact-projective-codensity-has-a-uniform-trace-square-gap` to `rho_n,V_n`.
For every fixed `a in A` (use the same theorem with `a` as the marked
element),

```text
1-|tr([V_n,rho_n(a)])|^2 = O((delta_n+epsilon_n)^2).          (ANP2)
```

Writing `A_j=alpha_(n,j)(a)`, the commutator in `(ANP2)` is block diagonal
with blocks `A_1 A_0^*` and `A_0 A_1^*`.  Its normalized trace is
`Re tr(A_0 A_1^*)`.  Thus `(ANP2)` forces

```text
|tr(A_0 A_1^*)| -> 1.                                       (ANP3)
```

One more fixed-word telescoping estimate replaces `A_j` by
`pi_(n,j)(a)`, proving `(ANV2)`.  All estimates are dimension-free.

