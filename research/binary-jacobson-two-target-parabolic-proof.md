---
rg: 2
id: binary-jacobson-two-target-parabolic-proof
kind: route
title: Write the two-target package as an upper block semidirect product
target: binary-jacobson-two-target-parabolic-is-marked-mf
requires:
  - binary-jacobson-monomial-symbol-preimage-is-marked-mf
  - amenable-implies-operator-mf
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

Use the block decomposition `J^5=J^I directSum J^Omega`.  For
`X in M_(3 x 2)(J)`, write

```text
n(X)=[[1_3,X],[0,1_2]].                                  (J2TP1)
```

Because the product of any two matrix units `E_(i alpha),E_(j beta)` with
`i,j in I` and `alpha,beta in Omega` is zero, root addition and commutation
give

```text
n(X)n(Y)=n(X+Y),             n(X)^(-1)=n(X)              (J2TP2)
```

in characteristic two.  Hence `N={n(X)}` is an abelian subgroup naturally
isomorphic to `M_(3 x 2)(J)` under addition.

An active-block matrix `a` and a target-block matrix `b` embed as
`diag(a,1_2)` and `diag(1_3,b)` and commute.  Direct multiplication gives

```text
diag(a,b) n(X) diag(a,b)^(-1)=n(a X b^(-1)).             (J2TP3)
```

Thus `A x B` normalizes `N`, and every named root into column `4` or `5`
belongs to `N`.  This proves containment in `(J2T1)`.  It also types every
Steinberg commutator created by the target-cycle roots: for example

```text
[x_(i4)(r),x_45(1)]=x_(i5)(r),
[x_(i5)(r),x_54(1)]=x_(i4)(r),                           (J2TP4)
```

and both outputs remain in the same abelian normal subgroup `N`.  No reverse
or diagonal root is generated.

The group `B=EL_2(F_2)=SL_2(F_2)` is finite.  The prerequisite makes `K`
amenable, hence its subgroup `A` is amenable.  Therefore `A x B` is amenable,
and the extension `N semidirect (A x B)` is amenable.  Every subgroup of it
is amenable as well.

Finally `x_24(Q)=n(X_Q)` for the matrix having its only nonzero entry `Q` in
position `(2,4)`.  The standard unilateral-shift representation of `J`
shows `Q != 0`, so this elementary root is nontrivial in `E`.  Its containing
amenable subgroup embeds faithfully into a norm matrix corona by
`amenable-implies-operator-mf`, proving marked MF visibility.
