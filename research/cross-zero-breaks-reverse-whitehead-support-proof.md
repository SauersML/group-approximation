---
rg: 2
id: cross-zero-breaks-reverse-whitehead-support-proof
kind: route
title: Count the symmetric difference after the mixed cross-zero square
target: cross-zero-breaks-reverse-whitehead-support-fusion
requires:
  - reverse-product-whitehead-fold-has-finite-fusion
  - outer-root-leavitt-table
---

The native root transports in `(CZR2)--(CZR3)` are fixed permutation-Weyl
words on spare Steinberg indices.  Applying them to both factors of each
partial Whitehead proves that the transported positive and opposite roots
carry the same coefficient occurrence, not merely the same central sign.
The Steinberg commutator formula then proves `(CZR4)` from `q_0q_1=0`.

In a scalar support fusion, every active coordinate contains the same base
packet over `F_2`.  If a coordinate lies in both `Omega_0` and `Omega_1`,
the two sides of `(CZR2)` evaluate there as

```text
x_12(1),                    x_23(1).
```

Their commutator is `x_13(1)`, which is nonidentity in the faithful finite
base packet.  Hence exactness of `(CZR4)` proves `(CZR5)`.

Root addition in the common `(1,4)` coordinate is multiplication of the
binary signs.  Thus `C_0C_1=J` says exactly that the parent active set is the
symmetric difference, proving `(CZR6)`.  Each branch partial Whitehead and
its mixed squares conjugate the entire parent packet to its child packet.
Conjugation preserves the total multiplicity weight, which proves
`(CZR7)` even when the finite coordinates carry unequal positive integer
multiplicities.

Let the common weight in `(CZR7)` be `r`.  Disjointness gives

```text
mu(Omega_A)=mu(Omega_0)+mu(Omega_1)=2r,
```

while `(CZR7)` gives `mu(Omega_A)=r`.  Hence `r=0`, so the parent mark is
identity.  This proves the claimed elimination of the complete scalar
support-fusion class.

