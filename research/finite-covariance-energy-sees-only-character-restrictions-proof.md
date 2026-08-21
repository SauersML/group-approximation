---
rg: 2
id: finite-covariance-energy-sees-only-character-restrictions-proof
kind: route
title: Block computation for finite covariance tests on an elementary-abelian PVM
target: finite-covariance-energy-sees-only-character-restrictions
requires: []
---

Let `tau` be the normalized trace and set

```text
w_(psi,chi)=||P_psi C P_chi||_2^2.
```

The two PVMs `(C P_chi C^*)_chi` and `(P_psi)_psi` resolve the identity.
Hence

```text
sum_psi w_(psi,chi)=tau(P_chi),
sum_chi w_(psi,chi)=tau(P_psi).                           (1)
```

Expanding the square of the difference of two projections and then summing
over `chi` gives

```text
sum_chi ||C P_chi C^*-P_(s chi)||_2^2
 =sum_chi (tau(P_chi)+tau(P_(s chi))-2w_(s chi,chi))
 =2 sum_(chi,psi!=s chi) w_(psi,chi).                     (2)
```

This proves `(FCR2)`.

On the block from `C P_chi C^*` to `P_psi`, the two selfadjoint involutions
`C rho(m) C^*` and `rho(s m)` have eigenvalues `chi(m)` and `psi(s m)`.
Their difference is zero when the signs agree and has squared modulus four
when they disagree.  Orthogonality of the blocks therefore gives

```text
d_m^2
 =4 sum_(chi,psi : chi(m)!=psi(s m)) w_(psi,chi).          (3)
```

Summing `(3)` over `m in T` proves `(FCR3)`.

Correct transport `psi=s chi` has
`psi(s m)=chi(m)` for every `m`, so it never occurs on the right side of
`(FCR3)`.  Every wrong block has `1<=h_T<=|T|` exactly when restriction to
`sT` separates the characters in `Omega`.  Comparing `(FCR2)` and `(FCR3)`
then yields `(FCR5)`.

Finally, suppose `psi!=psi'` have the same restriction to `sT`, and set
`chi=s^(-1)psi'`.  Then `s chi=psi'!=psi`, while for every `m in T`,

```text
chi(m)=psi'(s m)=psi(s m).
```

Thus the coordinate `(psi,chi)` has positive coefficient in `(FCR2)` and
coefficient zero in `(FCR3)`.  This proves the asserted kernel statement.
Since `(FCR4)` has at most `2^|T|` values, it cannot be injective on an
infinite `Omega`.

For the unitary realization with `s=1`, let `P_chi,P_psi` have trace `1/2`
and let `C` exchange their ranges.  Equality of the two restrictions makes
`C` commute with every `rho(m)`, `m in T`.  Neither spectral projection is
fixed, so `(2)` gives `E_1=2`.

For general abelian `M`, the calculation `(3)` has the same proof with the
coefficient four replaced by

```text
|chi(m)-psi(s m)|^2.
```

The image of an infinite character set in the finite torus `T^T` either has
a repeated point or has distinct points at arbitrarily small distance.
Choose such `chi,psi`, give their spectral projections trace `1/2`, and swap
them.  The transport energy remains two, while direct expansion of the
commutator gives exactly `(FCR6)`, which can be made arbitrarily small.
