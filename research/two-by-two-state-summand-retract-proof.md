---
rg: 2
id: two-by-two-state-summand-retract-proof
kind: route
title: Add a state summand and erase it by top-left compression
target: split-ucp-matrix-retracts-can-hide-defect-in-a-boundary-ideal
requires: []
---

Take `A=M_2`, let `phi(a)=<a e_1,e_1>` be the vector state, and identify
`B=M_2(A)=M_4`.  Define

```text
i(a)=diag(a,phi(a) I_2),
r([[x_11,x_12],[x_21,x_22]])=x_11.                       (SBR3)
```

Both maps are unital completely positive and `r i=id_A`.  Hence `i` is a
complete-order embedding: its inverse on `i(A)` is the completely positive
restriction of `r` (equivalently, the two complete contractions give equality
at every matrix norm level).

Let

```text
u=[[0,1],[1,0]].
```

Then `u` is a self-adjoint unitary generating `M_2` together with a diagonal
unitary, and `phi(u)=0`.  Therefore

```text
i(u)=diag(u,0),
d=1-i(u)^*i(u)=diag(0,I_2)>0,       r(d)=0.              (SBR4)
```

The projection `d` belongs to `C^*(i(A))`.  Multiplying `i(a)` by `1-d`
shows that every `diag(a,0)` belongs to that generated algebra, while `d`
supplies its second scalar summand.  Hence

```text
C^*(i(A))={diag(a,lambda I_2):a in M_2, lambda in C}
          ~= M_2 direct_sum C.                           (SBR5)
```

On `(SBR5)`, `r` is exactly the coordinate star-homomorphism
`M_2 direct_sum C -> M_2`; its kernel is the nonzero ideal `C d`.  The
operator system `i(A)` nevertheless has C-star envelope `A`: the extra
summand is a boundary ideal erased by the complete-order inverse.  This is
precisely the positive-kernel hiding allowed by `(OUR2)`.



