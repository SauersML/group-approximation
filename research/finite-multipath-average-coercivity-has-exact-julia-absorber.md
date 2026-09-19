---
rg: 2
id: finite-multipath-average-coercivity-has-exact-julia-absorber
kind: claim
title: A finite multipath average pays its full Gram disagreement or escapes through the Julia complement
distinct_from:
  two-path-holonomy-is-paid-by-corner-leakage: that gives the sharp relative-holonomy identity for two paths; this computes the complete pairwise Gram energy for any finite number of paths, including label--multiplicity-entangled paths.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that absorbs monomial finite-label paths by conjugate doubling; this treats a genuine additive same-block sum and shows that its universal absorber is complementary-carrier leakage.
  compact-hyperbolic-km-regular-microstates-synchronize: that must extract and control a native Kac--Moody carrier; this proves the analytic coercivity and the exact obstruction once such a multipath block is proposed.
---

**ESTABLISHED.**  Let `(M,tau)` be finite tracial, let `p,q` be projections
of the same positive trace, and let

```text
A_1,...,A_m in pMq,
A_i^*A_i=q,                 A_iA_i^*=p.                (MPA1)
```

Put `K=m^(-1) sum_i A_i`.  With trace and `L2` norm normalized on `qMq`,

```text
tau_q(q-K^*K)
 =1/(2m^2) sum_(i,j) ||A_i-A_j||_(2,q)^2.              (MPA2)
```

Let `Y` be any global unitary, `C=pYq`,
`L=q-C^*C=qY^*(1-p)Yq`, and
`delta=||C-K||_(2,q)`.  Then

```text
sum_(i,j) ||A_i-A_j||_(2,q)^2
 <=2m^2 tau_q(L)+4m^2 delta.                            (MPA3)
```

Thus a native relation which makes `C` nearly equal to the multipath average
and makes the carrier nearly invariant gives dimension-free consensus of all
paths.  The statement permits each `A_i` to entangle finite label and growing
multiplicity coordinates; no Schur factorization is used.

The leakage term is indispensable.  Every such `K` is a contraction, and its
Julia unitary has upper-left corner exactly `K`.  For that dilation,

```text
tau_q(L)=tau_q(q-K^*K)
        =1/(2m^2) sum_(i,j)||A_i-A_j||_(2,q)^2.          (MPA4)
```

Hence an additive same-block sum, even with arbitrary finite
label--multiplicity entanglement, has an exact finite-dimensional absorber
whenever the complementary carrier is unconstrained.  The smallest surviving
Kac--Moody coupling is therefore not addition alone: a named native relation
must also force same-corner invariance or charge the Julia leakage elsewhere.
