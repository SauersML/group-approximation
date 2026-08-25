---
rg: 2
id: commuting-double-commutator-has-direct-mark-overlap
kind: claim
title: A commuting double-commutator output overlaps the original involution
artifacts:
  - research/commuting-double-commutator-overlap-proof.md
distinct_from:
  involution-normal-product-forces-one-factor-overlap: that selects one carrier among the factors of an arbitrary bounded product; commutation of this double-commutator output with both conjugators makes all four factor overlaps equal and selects the original marked carrier itself.
---

Let `A,B,z,r` be self-adjoint involutions in a finite tracial von Neumann
algebra.  Suppose

```text
r=[[A,z],B],                    [r,A]=[r,B]=[r,z]=1,
P=(1-z)/2,                     Q=(1-r)/2.              (DCO1)
```

Then

```text
tau(QP) >= tau(Q)/4.                                   (DCO2)
```

The same conclusion is robust: if the double-commutator identity and the two
commutations hold up to `o(1)` in normalized Hilbert--Schmidt norm for
rounded involutions, then

```text
tau(QP) >= tau(Q)/4-o(1).                              (DCO3)
```

Unlike a generic normal-generation rank comparison, `(DCO2)` names the
unconjugated marked carrier `P`.  No Property T, stability theorem, or
literature input is used.

DERIVATION
commuting-double-commutator-overlap-proof
