---
rg: 2
id: six-weyl-sign-proper-moments-miss-top-parity
kind: claim
title: Every proper moment of the six Weyl root signs misses the top parity character
invalidates:
  - decode-six-top-sign-carrier-from-proper-moments
distinct_from:
  six-top-dyadic-root-signs-share-weyl-hexagon-carrier: that constructs the all-negative atom in the regular representation of the full last congruence layer; this gives a Weyl-covariant exact representation with the same proper sign moments but no all-negative atom.
  compression-signs-alone-do-not-fix-joint-multiplicity: that changes a three-bit joint spectrum through poor-margin compressions; this uses six exactly commuting involutions, no compression, and agrees with the regular character on every proper coordinate subset.
  six-shell-hecke-gap-is-blind-to-cross-chart-gram-energy: that separates six parahoric chart PVMs; this is already a one-chart obstruction before any denominator or cross-chart transporter is introduced.
---

**ESTABLISHED SHARP DECODER FIREWALL.**  Let `Phi` be the six ordered roots
of `A_2`.  Put

```text
Omega_-={epsilon in {+1,-1}^Phi : product_(alpha in Phi) epsilon_alpha=-1}
```

and let `H=l^2(Omega_-)`.  For `alpha in Phi`, define the commuting
involution

```text
U_alpha delta_epsilon=epsilon_alpha delta_epsilon.       (SPM1)
```

The determinant-one signed Weyl group acts on the order-two root signs by
permuting `Phi`: inversion of a sign has no effect.  Its permutation action
on `Omega_-` therefore gives unitaries `W_w` satisfying exactly

```text
W_w U_alpha W_w^*=U_(w alpha).                           (SPM2)
```

For every nonempty proper subset `S` of `Phi`, normalized trace on `H`
gives

```text
tr(product_(alpha in S) U_alpha)=0.                      (SPM3)
```

Indeed `Omega_-` is a coset of the even-parity subgroup of `{+1,-1}^6`.
The annihilator of that subgroup consists of only the empty and full
coordinate characters.  Hence every proper coordinate character averages
to zero on the coset.  On the other hand,

```text
product_(alpha in Phi) U_alpha=-I.                       (SPM4)
```

Consequently the all-negative joint projection is zero:

```text
D=product_(alpha in Phi) (I-U_alpha)/2=0.                (SPM5)
```

The excluded sign word `(-1,-1,-1,-1,-1,-1)` has even parity and therefore
does not belong to `Omega_-`.  Doubling `H` by a spectator makes its
dimension `64`, if desired, without changing any normalized trace.

By contrast, the regular representation of `(C_2)^6` has every nonempty
moment zero and `tr(D)=1/64`.  Thus the two packets agree on **all 62
nonempty proper sign-product moments**, as well as exact commutation and the
entire signed-Weyl covariance, but disagree maximally on the desired atom.

The missing datum is exactly one scalar.  For arbitrary commuting
involutions,

```text
tr(D)=2^(-6) sum_(S subseteq Phi) (-1)^|S|
          tr(product_(alpha in S) U_alpha).              (SPM6)
```

If all proper nonempty moments have their regular values, `(SPM6)` becomes

```text
tr(D)=2^(-6)(1+tr(product_(alpha in Phi) U_alpha)).       (SPM7)
```

Therefore any arbitrary-microstate decoding of the fixed `1/64` carrier
must control the full six-root parity word (or an equivalent genuinely
six-way joint statistic).  No collection of only proper-subset root moments,
even the complete collection with exact Weyl covariance, can do it.

This is not a countermodel to the arithmetic group or to denominator
transport: no `h` is represented.  It sharply precedes that issue.  After
the full parity moment authenticates positive `D`-mass, one still has to
transport that mass through the rectangular adjacent-depth map.  The point
is that denominator-depth analysis cannot manufacture a source carrier
from the 62 proper moments alone.
