---
rg: 2
id: finite-multipath-gram-julia-proof
kind: route
title: Expand the average Gram matrix and dilate the resulting contraction
target: finite-multipath-average-coercivity-has-exact-julia-absorber
requires:
  - two-path-holonomy-is-paid-by-corner-leakage
---

Expanding the ordered pairwise sum and using `(MPA1)` gives the operator
identity

```text
1/(2m^2) sum_(i,j) (A_i-A_j)^*(A_i-A_j)
 =q-1/m^2 sum_(i,j) A_i^*A_j
 =q-K^*K.                                               (MPA5)
```

Taking `tau_q` proves `(MPA2)`.  Positivity of the left side also shows that
`K` is a contraction.

Since `C^*C=q-L`,

```text
tau_q(q-K^*K)
 <=tau_q(L)+||C^*C-K^*K||_(1,q).
```

Both `C` and `K` are contractions, so normalized Schatten Holder gives

```text
||C^*C-K^*K||_(1,q)
 <=(||C||_(2,q)+||K||_(2,q))||C-K||_(2,q)
 <=2 delta.                                             (MPA6)
```

Combining `(MPA2)` and `(MPA6)` yields `(MPA3)`.

Finally apply the Julia unitary `(TPH8)` from
`two-path-holonomy-is-paid-by-corner-leakage` to the contraction `K`.  Its
upper-left compression is `K`, and the source leakage is exactly
`q-K^*K`.  Taking `tau_q` and using `(MPA2)` proves `(MPA4)` and the exact
absorber assertion.
