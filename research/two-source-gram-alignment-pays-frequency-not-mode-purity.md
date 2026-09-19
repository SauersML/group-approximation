---
rg: 2
id: two-source-gram-alignment-pays-frequency-not-mode-purity
kind: claim
title: Two-source Gram alignment pays a common frequency ledger but not cyclic mode purity
distinct_from:
  bs14-source-mode-reset-has-exact-frequency-cost: that computes the exact cost after one cyclic eigenmode has been selected; this aligns two supplied source isometries and shows that inversion controls their aggregate frequency, but also proves that these data do not select one mode.
  bs14-trivial-boundary-inversion-forces-r-fixed-source: that derives the exact block equation RB=B in a neutral dilation; this is the quantitative approximate source calculation and its low-frequency counterpacket.
  two-cubic-residual-carriers-recover-the-deleted-source: that recovers a source as an intersection under a carrier-angle gap; this assumes two source isometries have been extracted and polar-aligns them without an angle hypothesis.
---

**ESTABLISHED, WITH A SHARP FIREWALL.** Let `R` be unitary on `H`, and let

```text
B_1,B_2:E -> H
```

be isometries of the same finite source space.  Put `T=B_1^*B_2` and choose
a polar decomposition

```text
T=A V,                 A=(T T^*)^(1/2),                 (TSG1)
```

extending the polar partial isometry `V` to a unitary on `E`.  Set

```text
B_2'=B_2 V^*,
C=(B_1+B_2')/2,
H_0=((1+A)/2)^(1/2),
W=C H_0^(-1).                                            (TSG2)
```

Then `B_1^*B_2'=A>=0`, `C^*C=H_0^2`, and `H_0>=2^(-1/2)`.  Hence `W` is
an isometry and

```text
||B_1-W||_F^2+||B_2'-W||_F^2
 =4 Tr(1-H_0)
 <=2 Tr(1-A)
 =||B_1-B_2'||_F^2.                                    (TSG3)
```

Thus the cross-Gram defect pays, with no principal-angle denominator, for
replacing the two candidate sources by one literal common source.

The same common source has the exact inversion-frequency estimate

```text
||(R-1)W||_F^2
 <=||(R-1)B_1||_F^2+||(R-1)B_2||_F^2.                  (TSG4)
```

Indeed `||H_0^(-1)||<=sqrt(2)` and

```text
||(R-1)C||_F^2
 <=(1/2)(||(R-1)B_1||_F^2+||(R-1)B_2'||_F^2).
```

If `R=sum_j lambda_j P_j`, `(TSG4)` is precisely the common source-mode
ledger

```text
sum_j |1-lambda_j|^2 ||P_j W||_F^2
 <= sum_(i=1)^2 ||(R-1)B_i||_F^2.                       (TSG5)
```

The phase rotation on the source of `B_2` does not change its inversion
cost.  In the BS14 boundary problem, once the two cubic polar carriers have
actually supplied source isometries, the approximate inversion block row
therefore pays their direct cyclic-frequency cost, while the cross-Gram row
pays their synchronization.  This is the desired finite-packet analytic
ledger up to the remaining **mode-purity/integrality** step.

## Low-frequency mode-purity counterpacket

The right side of `(TSG3)--(TSG5)` cannot also control the distance to one
resettable cyclic mode.  Take a multiplicity-one length-`m` scalar BS packet
with return phase one.  Let `f_0,...,f_(m-1)` be the Fourier eigenvectors of
its cyclic implementer `R`, so

```text
R f_j=exp(2 pi i j/m)f_j.
```

For `E=C`, take identical source isometries

```text
B_1(1)=B_2(1)=w_m=(f_0+f_1)/sqrt(2).                    (TSG6)
```

Their Gram defect is zero, while

```text
||(R-1)w_m||^2
 =(1/2)|exp(2 pi i/m)-1|^2=O(m^(-2)).                   (TSG7)
```

Nevertheless `w_m` stays a fixed distance from the fixed source of **every**
exact covariance implementer on the same simple `S`-orbit.  Such an
implementer is a weighted cyclic shift, and every fixed unit vector of a
weighted cyclic shift has constant coordinate modulus `m^(-1/2)` in the
`S`-eigenbasis.  Conversely every flat unit vector is the fixed vector of
some return-one weighted shift.  Therefore

```text
inf_(z flat) ||w_m-z||^2
 =2-(2/sqrt(m)) ||w_m||_1
 -> 2-4 sqrt(2)/pi >0.                                  (TSG8)
```

Here

```text
|w_m(k)|=sqrt(2/m)|cos(pi k/m)|
```

and the limit in `(TSG8)` is the Riemann sum for `|cos|`.

Consequently there is no dimension-independent inequality of the form

```text
distance to a single exact reset source squared
 <= C (inversion frequency + two-source Gram defect).    (TSG9)
```

Low adjacent cyclic modes defeat it even when the two carriers already
agree exactly.

## Scope for the active dilation

This counterpacket does not refute qualitative flexible repair: it occupies
only one direction in a length-`m` packet and can be discarded at normalized
cost `m^(-1/2)`.  It proves that the common-source ledger must retain the
active/passive rank payment from
`bs14-energy-threshold-active-passive-ledger`.  Inversion plus cross-Gram
energy synchronizes source maps and controls their frequency, but cannot by
itself round a low-frequency band to the one-mode-per-simple-packet integer
capacity required by `bs14-source-mode-reset-has-exact-frequency-cost`.

The remaining theorem must therefore do one of two additional things:

1. discard spectrally spread low-frequency sources using the existing
   passive rank budget; or
2. split them across duplicated packet copies and charge that integer
   duplication to a separate carrier-rank/Gram defect.

No proof may charge that final operation only to `(TSG3)--(TSG5)`.
