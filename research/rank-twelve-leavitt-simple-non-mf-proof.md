---
rg: 2
id: rank-twelve-leavitt-simple-non-mf-proof
kind: route
title: Compress a rank-three Kazhdan corner inside four blocks and use the torsion active core
target: rank-twelve-leavitt-simple-non-mf
requires:
  - kazhdan-asymptotic-commutant-transport
  - elementary-group-property-t-over-free-algebras
  - binary-leavitt-elementary-group-is-simple
  - torsion-normal-generator-mf-shadow-equivalence
  - compression-defect-dies-in-finite-dimensions
---

Put `p=s_0*t_0` and `q=s_1*t_1`.  On `M_3(R)`, the map

```text
Psi(A)=q*I_3+s_0*A*t_0
```

is a unital injective endomorphism.  Define the `6 x 6` inverse pair

```text
U=[[s_0 I_3, s_1 t_0 I_3], [0, t_1 I_3]],
V=[[t_0 I_3, 0], [s_0 t_1 I_3, s_1 I_3]].
```

The Leavitt relations give `UV=VU=I_6`.  The Whitehead identity writes
`tau=diag(U,V)` as six block-unipotent matrices, hence as a product of
elementary `12 x 12` matrices.  Conjugation by `tau` sends the upper-left
`EL_3(R)` into itself and implements `Psi` there.

The root `c=e_34(1)` centralizes the upper-left source, while direct block
multiplication gives

```text
tau*c*tau^-1=e_01(q)e_34(1).
```

Consequently, for `ell=e_12(1)`,

```text
d=[tau*c*tau^-1,ell]=e_02(q).
```

The coefficient `q` is nonzero because `t_1*q*s_1=1`.  In characteristic
two, `d` is an involution.  The group `EL_12(R)` is nontrivial and simple, so
the nonidentity element `d` normally generates it.

The rank-three source has property `(T)`.  One-sided Kazhdan transport makes
`d` universally Hilbert--Schmidt trivial in every operator-norm asymptotic
representation.  The finite-order normal-generator equivalence places `d`
in the MF radical, and simplicity gives `Rad_MF(H)=H`.

For an exact finite-dimensional linear representation over any field, the
finite-dimensional commutant argument kills `d`; simplicity again kills the
whole representation.
