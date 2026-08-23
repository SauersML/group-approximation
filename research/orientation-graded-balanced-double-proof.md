---
rg: 2
id: orientation-graded-balanced-double-proof
kind: route
title: Tensor a marked representation with the two orientation characters
target: orientation-graded-mixed-returns-have-a-balanced-double
requires:
  - controlled-fine-reflection-superrank-orientation-law
  - balanced-controlled-whitehead-return-checksum
---

Let `chi_0,chi_1` be the two one-dimensional unitary representations of
`C_2`.  Equation `(OGM2)` is the direct sum

```text
(rho_0 tensor chi_0 o chi) direct_sum
(rho_0 tensor chi_1 o chi),
```

so it is an exact representation of every relation of `Gamma`.  Since
`chi(J)=0`, the value of the central mark is unchanged.

On a literal marked spin summand, the first character leaves the controlled
reflection `C` unchanged and the second changes its sign, while both leave
the Pauli subgroup fixed.  This proves `(OGM3)`.  If `W in ker(chi)`, both
characters take value one on `W`, so its action on the added two-dimensional
orientation factor is the identity.

The controlled orientation law now gives `c_P=1/16`, `c_G=1/32`.  The
balanced-return checksum says that conjugating by any such `W` leaves at
least `1/32` normalized adjoint mass outside the controlled fixed range.
Thus no exact consequence of the grading-preserving presentation can assert
the missing range identification.

