---
rg: 2
id: cross-zero-breaks-reverse-whitehead-support-fusion
kind: claim
title: A shared reverse-product cross-zero row breaks every scalar support fusion
artifacts:
  - research/cross-zero-breaks-reverse-whitehead-support-proof.md
distinct_from:
  reverse-product-whitehead-fold-has-finite-fusion: that realizes the nonlinear Whitehead fold on three overlapping scalar packet supports; this transports the very same reverse-product occurrences into composable roots and uses their crossed-zero product to forbid every overlap.
  first-cousin-cross-arm-breaks-three-state-reuse: that rejects one periodic Pauli cousin collision but permits fresh factors for every finite cross table; this combines one cross row with equal-weight parent/child Whitehead conjugacy and the completeness symmetric-difference equation, ruling out the whole scalar support category at fixed size.
  full-completeness-opposite-menu-has-finite-gl5-fusion: that transports complete payload packets between three support charts; this adds a mixed square which exposes their unavoidable common active coordinate to a nontrivial composable-root commutator.
---

**ESTABLISHED SUPPORT-FUSION ELIMINATION.**  Retain the shared reverse-product
occurrences

```text
C_i=x_14(q_i),          D_i=x_41(q_i),
W_i=C_iD_iC_i,          C_0C_1=J,                     (CZR1)
```

from `reverse-product-whitehead-fold-has-finite-fusion`.  Use fixed native
Weyl words `U_0,U_1` to put those same coefficients in composable roots:

```text
A_0=U_0C_0U_0^(-1)=x_12(q_0),
B_1=U_1C_1U_1^(-1)=x_23(q_1).                         (CZR2)
```

Include the opposite-factor mixed squares as well,

```text
U_0D_0U_0^(-1)=x_21(q_0),
U_1D_1U_1^(-1)=x_32(q_1),                             (CZR3)
```

so `(CZR2)` cannot be implemented by transporting only the scalar fold
labels while leaving the opposite-root payload elsewhere.  Since
`q_0q_1=0`, the actual Steinberg row is

```text
[A_0,B_1]=x_13(q_0q_1)=1.                             (CZR4)
```

The three-packet model `(RWF5)` fails `(CZR4)`: its child supports overlap
in the first `K` coordinate, where the two transported letters are
`x_12(1),x_23(1)` and their commutator is the nonidentity `x_13(1)`.

More strongly, no finite scalar character-support fusion of this kind can
satisfy all the rows with the mark surviving.  Let `Omega_i` be the active
support of the complete `(C_i,D_i)` packet and `Omega_A` the parent support.
The mixed squares make `(CZR4)` coordinatewise scalar, so

```text
Omega_0 intersect Omega_1=empty.                       (CZR5)
```

The fold says

```text
Omega_A=Omega_0 symmetric_difference Omega_1.          (CZR6)
```

Native partial-Whitehead transport makes the child and parent packets
unitarily conjugate, hence their normalized support weights are equal:

```text
mu(Omega_0)=mu(Omega_1)=mu(Omega_A).                   (CZR7)
```

Equations `(CZR5)--(CZR7)` imply `mu(Omega_A)=0`.
Therefore the marked parent packet vanishes in every finite scalar support
fusion, independent of the number of coordinates or their multiplicities.

This is genuine progress beyond the three-packet fence, but it is not yet
`(BAC1)`.  An arbitrary finite unitary model need not decompose the mixed
squares into scalar active/inactive packet coordinates; non-scalar internal
holonomy could make the two transported root letters commute on a common
carrier without either whole packet vanishing.  The remaining target is a
matrix-only lemma promoting `(CZR2)--(CZR4)` to the same intersection-zero
conclusion for arbitrary exactified payload packets.

No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis, or
literature result is used.

DERIVATION
cross-zero-breaks-reverse-whitehead-support-proof

