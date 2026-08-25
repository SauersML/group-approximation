---
rg: 2
id: atlas-five-row-h-bridge-equivalence-proof
kind: route
title: Compare the two fixed quadratic forms on their common finite-packet kernel
target: atlas-five-row-energy-equals-h-bridge-energy
requires:
  - regular-atlas-boundary-tangent-is-h-fixed
  - regular-atlas-linearized-h-coercivity
---

On one regular packet let

```text
L=sum_(j in J) B_j^*B_j,
K=sum_(ell=1)^4 C_ell^*C_ell,
```

where `B_j X=rho(z_j)X` and
`C_ell X=rho(t_ell)X-Xrho(t_ell)`.  The established common-kernel theorem
gives

```text
ker(L)=ker(K)=rho(H)'.                                  (FBP1)
```

On the orthogonal complement of this kernel, both forms are positive
definite on one fixed finite-dimensional space.  The minimum and maximum of
their generalized Rayleigh quotient are therefore positive and finite.
Thus

```text
c_H K<=L<=C_H K.                                       (FBP2)
```

Both operators amplify by the identity on the external multiplicity space,
so the same constants prove `(FBE2)` for every `k`.  The first inequality is
also the previously recorded linearized coercivity; the compactness argument
supplies the reverse inequality.

For `(FBE3)`, use `i_1(t)=rho(t)` and
`i_2(t)=U rho(t)U^*` (the opposite convention gives the same norm).  Then

```text
pi_U(b_ell)=U rho(t_ell)U^*rho(t_ell)^*.
```

Right multiplication by the unitary `rho(t_ell)U` turns
`pi_U(b_ell)-1` into
`U rho(t_ell)-rho(t_ell)U`, proving equality of the normalized
Hilbert--Schmidt norms.  Substitution into `(FBP2)` proves the final
equivalence.
