---
rg: 2
id: ghost-completed-fano-naimark-wordizer-proof
kind: route
title: Add the ghost channel and use one dihedral commutator
target: ghost-completed-fano-naimark-wordizes-one-local-predicate
requires:
  - fano-cap-sequential-products-form-an-algebraic-naimark-carrier
  - shared-multiplicity-commutator-builds-selected-hybrid-row
---

Equation `(GCN2)` follows by evaluating the left side on each atomic
projection: its coefficient is four for `t!=0` and zero for `t=0`.
Orthogonality of `F` and all `E_lambda` then gives

```text
V^*V=(1/4)sum_lambda E_lambda+F=1.
```

The ghost row of `V` is `F`, while every cap row annihilates `F`; hence
`L_gV=VF`.  Multiplying by `V^*` proves `(GCN4)`, including
`L_gQ=VF V^*=QL_g`.

For honest `t`, the vector `(GCN5)` has norm one and is orthogonal to the
ghost coordinate.  A Householder reflection takes `e_s` to `v_t` while
acting only on their span, so it fixes the ghost axis.  The block sum in
`(GCN6)` is therefore a self-adjoint unitary and its `e_s` column is exactly
`(GCN3)`.

On the ghost two-plane, in the ordered basis `(e_s,e_g)`,

```text
Z=diag(1,-1),                 W_0=[[0,1],[1,0]].
```

Thus `(ZW_0)^2=-I_2`.  On all honest blocks `Z` and `W_t` commute.  Therefore

```text
C-1=-2 F tensor (projection onto span{e_s,e_g}).
```

Its squared normalized Hilbert--Schmidt norm is
`4*(2/8)*tau(F)=tau(F)`, proving `(GCN8)`.  Relations `(GCN9)` prove the
finite dihedral factorization; a finite matrix amplification of the finite
group algebra supplies any required representation multiplicities.
