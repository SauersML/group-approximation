---
rg: 2
id: group-sos-certificate-survives-hs-adjoint-microstates
kind: claim
title: Finite group-algebra SOS certificates survive normalized-HS adjoint microstates with linear residual
---

Let `Gamma` be a group and let `Delta=Delta*` and
`xi_1,...,xi_r in C[Gamma]` have finite support and satisfy

```text
Delta^2 - kappa Delta = sum_j xi_j* xi_j.               (SOS)
```

Let `F subset Gamma` contain every element and product needed to expand this
identity. Suppose `phi:F->U(d)` is inverse-normalized and every tested product
has normalized-HS defect at most `delta`. On `H=M_d(C)` put

```text
T_g=Ad(phi(g)),
L_phi(sum_g a_g g)=sum_g a_g T_g,
A=L_phi(Delta),
X_j=L_phi(xi_j).
```

Then `L_phi` respects `*` exactly and

```text
||A^2-kappa A-sum_j X_j*X_j||_(2,H)
 <= sqrt(2) delta (||Delta||_1^2+sum_j||xi_j||_1^2).    (ASOS)
```

If `Delta` is the usual Laplacian of a finite inverse-closed generating set,
then `A>=0`. The bound is independent of matrix dimension.
