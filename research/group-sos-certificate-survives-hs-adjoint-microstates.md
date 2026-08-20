---
rg: 2
id: group-sos-certificate-survives-hs-adjoint-microstates
kind: claim
title: Finite group-algebra SOS certificates survive normalized-HS adjoint microstates with linear residual
---

Let `Gamma` be a group and let `Delta=Delta*` and
`xi_1,...,xi_r in C[Gamma]` have finite support and satisfy the exact identity

```text
Delta^2 - kappa Delta = sum_j xi_j* xi_j               (SOS)
```

for some `kappa>0`.  Let `F subset Gamma` be finite and contain every group
element appearing in `Delta`, the `xi_j`, their inverses, and every product
needed to expand `Delta^2` and `xi_j*xi_j`.

Suppose `phi:F->U(d)` is inverse-normalized,

```text
phi(1)=I,
phi(g^(-1))=phi(g)*,
```

and on every product used above satisfies

```text
d_2(phi(g)phi(h),phi(gh)) <= delta.
```

On the Hilbert space `H=M_d(C)` with normalized Hilbert--Schmidt inner product,
put

```text
T_g = Ad(phi(g)),
L_phi(sum_g a_g g)=sum_g a_g T_g,
A=L_phi(Delta),
X_j=L_phi(xi_j).
```

Write `||.||_(2,H)` for normalized Hilbert--Schmidt norm on `B(H)`, whose
normalized trace has dimension `d^2`.  Then `L_phi` respects `*` exactly and

```text
|| A^2-kappa A-sum_j X_j*X_j ||_(2,H)
 <= C_SOS delta,                                        (ASOS)
```

where

```text
C_SOS = sqrt(2) * ( ||Delta||_1^2 + sum_j ||xi_j||_1^2 )
```

and `||sum a_g g||_1=sum |a_g|`.

If `Delta` is the usual Laplacian of a finite inverse-closed generating set,
then `A>=0`.  The estimate is independent of the matrix dimension.  It is the
finite-window bridge from a property-`(T)` SOS certificate to spectral
information about the adjoint action of a normalized-HS microstate.
