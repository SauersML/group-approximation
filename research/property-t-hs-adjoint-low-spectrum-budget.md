---
rg: 2
id: property-t-hs-adjoint-low-spectrum-budget
kind: claim
title: Property T gives a vanishing spectral budget for low-energy adjoint directions of HS microstates
---

Let `Gamma` have property `(T)` and let `S` be a finite inverse-closed
generating set.  There are `kappa>0`, a finite multiplication window `F`, and
a constant `C<infinity`, depending only on `(Gamma,S)`, with the following
property.

For every inverse-normalized normalized-HS `delta`-microstate `phi` on `F`,
let `H=M_d(C)` and define the positive adjoint Laplacian

```text
A_phi = I - (1/|S|) sum_(s in S) Ad(phi(s))
```

on `H`.  Give `B(H)` its normalized trace `Tr_H/d^2`.  If

```text
P_low = 1_[0,kappa/2](A_phi),
```

then

```text
tr_H(P_low A_phi) <= C delta,
tr_H(P_low sqrt(A_phi)) <= sqrt(C delta).              (PTB1)
```

Moreover every fixed closed interval `[a,b] subset (0,kappa)` satisfies

```text
tr_H(1_[a,b](A_phi)) <= C_(a,b) delta^2.               (PTB2)
```

Thus a property-`(T)` microstate may have many almost-central adjoint
directions, including the vanishing-rank spike directions invisible to any
fixed word test, but their *aggregate low spectral energy* is forced to zero.
This is stronger information than a bare spectral-gap statement and is a
natural global potential for the live recursive HS-refinement problem.
