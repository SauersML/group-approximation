---
rg: 2
id: bs14-native-cell-padding-preserves-lattice-charge
kind: claim
title: Same-support BS14 cell padding cannot repair a saturation-lattice charge
distinct_from:
  bs14-two-exit-typed-transport-is-not-saturated: that exhibits a fractional hole and determinant two; this distinguishes multiplicative saturation from additive flexible padding.
  additive-index-instability: that concerns determinant phases under matrix amplification; this is the exact affine-semigroup lattice of joint source/two-exit cells.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for an analytic operator repair; this proves which combinatorial padding operation cannot supply it.
---

Let `E` be any fixed native support of admissible source/two-exit cells, let
`A_E` be its three-partite incidence matrix, and put

```text
S_E=A_E N^E,                 L_E=A_E Z^E.             (NCP1)
```

If an integral margin vector `b` lies outside `L_E`, then no amount of
padding by cells from the same support can repair it:

```text
b+s notin S_E        for every s in S_E.              (NCP2)
```

Indeed `S_E` is contained in `L_E`, while `b+s` and `b` represent the same
class in `Z^(I+J+K)/L_E`.  Thus a bounded saturation exponent

```text
q b in S_E
```

does **not** imply a bounded additive-padding theorem.  Multiplying the
whole approximate model by `q` is a different operation from adjoining
exact native cells.

For the even-parity support `(TET4)`, label the two vertices in every row
family by bits zero and one.  The functional

```text
omega(b)=sum_i i s_i + sum_j j e^(1)_j
                         + sum_k k e^(2)_k  mod 2     (NCP3)
```

vanishes on every allowed cell, hence on `L_E`.  The six-unit margin vector
from `(TET6)` has `omega=1`; therefore it remains nonintegralizable after
**arbitrarily much** same-support padding, even though twice that vector is
in `S_E`.  This is an infinite additive-padding ratio, not merely a missing
factor of two.

One odd-parity cell changes `omega` and removes this particular lattice
charge.  Consequently the useful bounded-repair question is not a
saturation-exponent question.  It is whether the native BS14 operator
relations provide, for every torsion charge arising after type rounding, a
support-enlarging compatible cell whose dimension and displacement are
charged by the active energy.  Equivalently, one needs a bound on the
distance to the semigroup after permitting controlled **type changes**, not
after adding elements of the original semigroup.

The `v!=1` active sector is even more sharply separated.  It supplies no
source row at all because `Fix(R)=0`; energy-paid removal of such a mode is
necessarily an internal perturbation/type change and cannot be encoded as
padding in `(NCP1)`.  The singular-value rank ledger pays its vector-space
size, but the BS-invariant-hull obstruction still prevents that ledger from
being promoted automatically to an exact internal repair.

