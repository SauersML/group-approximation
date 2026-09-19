---
rg: 2
id: a4-canonical-coherence-data-hs-lipschitz
kind: claim
title: The canonical regular-A4 coherence projections and transports are uniformly HS-Lipschitz in the generators
---

Let `rho,rho'` be exact regular-multiple representations of

```text
A4=<a,b | a^3=b^2=(ba)^3=1>
```

on the same finite-dimensional Hilbert space.  Form the canonical data

```text
P_j, Q_+, E_j, R_j=P_j-E_j,
S=Q_+-sum_j E_j,
T_j=sqrt(3) S R_j
```

from `a4-line-carriers-explicit-idempotents` and
`a4-regular-three-way-coherence-transducer`, and form the primed data from
`rho'`.

There is a constant `C_fan`, depending only on `A4` and not on the number of
regular copies, such that

```text
max_j (
  ||P_j-P'_j||_2 + ||E_j-E'_j||_2 + ||R_j-R'_j||_2
  + ||T_j-T'_j||_2
) + ||Q_+-Q'_+||_2 + ||S-S'||_2

<= C_fan (||rho(a)-rho'(a)||_2 + ||rho(b)-rho'(b)||_2).   (A4-FAN-LIP)
```

Thus the qutrit/multiplicity compiler is not merely canonical algebraically:
it is dimension-free stable in normalized Hilbert--Schmidt norm.  In
particular, near-identical exact A4 contexts have near-identical carrier
projections and near-identical partial-unitary identifications of their
multiplicity wires.