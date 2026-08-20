---
rg: 2
id: property-t-hs-adjoint-low-spectrum-budget-proof
kind: route
title: Push Ozawa's finite SOS certificate through the adjoint microstate
target: property-t-hs-adjoint-low-spectrum-budget
requires:
  - property-t-laplacian-sos-certificate
  - group-sos-certificate-survives-hs-adjoint-microstates
  - positive-sos-residual-spectral-budget
---

Take the symmetric probability measure which is uniform on `S`; its Laplacian
is

```text
Delta = 1 - (1/|S|) sum_(s in S) s.
```

By `property-t-laplacian-sos-certificate`, choose `kappa>0` and finitely many
`xi_j` with

```text
Delta^2-kappa Delta=sum_j xi_j*xi_j.                    (1)
```

Let `F` contain the finite supports and products occurring in `(1)`.  For a
`delta`-microstate on this window,
`group-sos-certificate-survives-hs-adjoint-microstates` applied to `(1)` gives

```text
A_phi^2-kappa A_phi-B_phi=R_phi,
B_phi=sum_j X_j*X_j >= 0,
||R_phi||_(2,H) <= C_SOS delta,                          (2)
```

where

```text
C_SOS=sqrt(2)(||Delta||_1^2+sum_j||xi_j||_1^2).
```

The same theorem gives `A_phi>=0`: inverse-closure of `S` makes the adjoint
Laplacian the Dirichlet operator

```text
< A_phi z,z >
 = (1/(2|S|)) sum_s ||Ad(phi(s))z-z||_2^2.
```

Apply `positive-sos-residual-spectral-budget` to `(2)` with
`eta=C_SOS delta`.  It yields

```text
tr_H(P_low A_phi) <= (2 C_SOS/kappa) delta,
tr_H(P_low sqrt(A_phi))
 <= sqrt((2 C_SOS/kappa) delta).
```

This is `(PTB1)` after setting `C=2 C_SOS/kappa`.

For a fixed `[a,b] subset (0,kappa)`, the same prerequisite gives

```text
tr_H(1_[a,b](A_phi))
 <= (C_SOS/c(a,b))^2 delta^2,
```

where `c(a,b)=min(a(kappa-a),b(kappa-b))>0`.  This is `(PTB2)`.

Every constant and the required multiplication window are fixed once the
finite SOS certificate is chosen; none depends on `d` or on the microstate.
