---
rg: 2
id: atlas-even-gram-does-not-pay-toeplitz-exit
kind: claim
title: Existing phase-even Atlas Gram coordinates do not pay the Toeplitz exit
distinct_from:
  involutive-compression-gram-ledger-has-unit-loss: that isolates the positive Toeplitz leakage L and the stationary complement e; this tests the concrete Atlas phase-even coordinates as the missing mixed support test.
  atlas-mixed-c3-gram-has-local-zero-interval: that computes the local range of one gauge-invariant Atlas leakage; this compares its carrier and zero fiber with the Toeplitz branch projection.
  transported-coefficient-corners-share-flat-quarter-carrier: that constructs a canonical common quarter projection; this proves it is not the Schur child exit and q14 does not supply the missing identification.
---

# Existing phase-even Atlas Gram coordinates do not pay the Toeplitz exit

ESTABLISHED. Let `e` be the unused corrected-child projection in the binary
Toeplitz head and let

```text
L=p h(1-p)h p=p-(php)^2                               (AEG1)
```

be the positive leakage of an involutive closed return. The desired mixed
support estimate is

```text
tau(e) <= C tau(L)+C E_packet,                         (AEG2)
```

with `E_packet` a sum of ordinary Atlas/Schur relator defects.

None of the three existing phase-even Atlas coordinates has the required
incidence.

First, the canonical transported common carrier `F` has trace `1/4`, but it
is not a corrected-child projection. Its exact fingerprints are

```text
Fq != F,
dist_2(F,A_raw)^2=23/128,
dist_2(F,A_comb)^2=7/32,                                (AEG3)
```

and it commutes with none of the eight raw/comb character cuts. In contrast,
`e` is a reducing atom of the corrected Schur child algebra. Thus identifying
`e` with `F`, or even placing `F<=e`, is a new carrier-membership decoder; it
is not a consequence of the packet trace table, collision, or q14.

Second, the gauge-invariant mixed `C_3` Gram scalar

```text
Lambda(U)=||Z(U)-PZ(U)P||_2^2                           (AEG4)
```

is a plausible numerical surrogate for `tau(L)`, but collision and exact
regular local profiles permit

```text
q_19243(U_theta)=1,
Lambda(U_theta)=sin(2theta)^2 Lambda_*.                 (AEG5)
```

At `theta=0`, `Lambda=0` while the regular Schur/Toeplitz branch profile has
positive `e`. Hence collision plus regular profile data cannot imply
`(AEG2)`. This is an exact finite-dimensional countermodel to the
**profile-relaxed** inequality. It is not asserted to solve all twelve
common-product packet equations; that is precisely why a full simultaneous
Atlas lift remains a possible matrix-only input.

Third, q14 supplies the sharp opposite-direction estimate

```text
x_30(U)^2 >= 1/2-(1+sqrt(2)) epsilon_14(U).             (AEG6)
```

This is a positive covariance wall, not relator energy tending to zero. To
use it for `(AEG2)` one needs a new upper transfer

```text
x_30(U)^2 <= C tau(L)+C E_packet.                       (AEG7)
```

No such universal finite-tracial inequality can hold. The exact augmented
packet-plus-19243-plus-q14 finite-factor model has all relator defects zero
and `x_30^2=1`. Tensor it with the stationary Toeplitz spectator from
`(ICG4)`. Then

```text
E_packet=0,       L=0,       tau(e)>0,       x_30^2=1.  (AEG8)
```

Thus neither `(AEG2)` nor `(AEG7)` follows from positivity, conditional
expectations, projection-Gram identities, or any trace-polynomial argument
valid in all finite tracial von Neumann algebras. Counting `x_30^2` itself as
the exit payment does not help: it stays positive in an exact marked model
and therefore is not a vanishing approximation defect.

The conclusion is deliberately narrower than a matrix no-go. A genuinely
finite-dimensional spectral/rank selection could correlate a chosen Atlas
block with `e` even though the exact factor model cannot. That possibility is
exactly `atlas-wedderburn-soft-transport-certificate`. But collision, q14,
the fixed common quarter carrier, and the current mixed `C_3` Gram do not by
themselves provide the Toeplitz mixed support test.
