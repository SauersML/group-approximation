---
rg: 2
id: fourth-power-covariance-unfolds-square-root-branches
kind: claim
title: The BS fourth-power row promotes square alignment to root alignment
distinct_from:
  relative-first-triangle-rounding-has-an-odd-root-branch-firewall: that shows square alignment alone loses a positive-density odd root branch; this proves that simultaneous alignment of the BS implementer charges exactly that branch.
  same-core-involution-cubic-gauge-coercivity: that coerces an extending-involution gauge already lying in the root commutant; this is a linear root-lifting estimate for BS cores and does not assume an extender.
  bs14-exact-representation-variety-is-hs-locally-rigid: that controls two close exact BS representations by packet classification; this derives root closeness directly from only the implementer and squared-root coordinates.
---

Let `(R,S)` and `(R',S')` be exact finite-dimensional `BS(1,4)`
representations on the same space:

```text
R S R^*=S^4,                 R' S' R'^*=S'^4.        (FPC1)
```

Then, in normalized Hilbert--Schmidt norm,

```text
||S-S'||_2
 <=2||S^2-S'^2||_2+2||R-R'||_2.                      (FPC2)
```

More generally, for one exact core `(R,S)` and every matrix `C`,

```text
||[C,S]||_2
 <=2||[C,S^2]||_2+2||[C,R]||_2.                      (FPC3)
```

Both constants are independent of dimension, the odd order of `S`, its
fourth-power orbit lengths, and all multiplicities.  Thus the square-root
branch is not an additional authentication problem once a correction has
simultaneously aligned the fourth-power implementer `R` and the squared root
`S^2`.

In particular, if `U` is unitary, then

```text
||USU^*-S||_2
 <=2||US^2U^*-S^2||_2+2||URU^*-R||_2.                (FPC4)
```

Apply this to the Hadamard branch rotation in
`relative-first-triangle-rounding-has-an-odd-root-branch-firewall`.  There
`Q_p=US^2U^*` obeys `||Q_p-S^2||_2<=2 pi/p`, whereas

```text
||USU^*-S||_2
 >=sqrt((p-1)/p) cos(pi/(2p)).                         (FPC5)
```

Consequently that wrong positive-density branch pays the explicit
implementer displacement

```text
||URU^*-R||_2
 >=(1/2)sqrt((p-1)/p) cos(pi/(2p))-2 pi/p,             (FPC6)
```

whose lower limit is `1/2`.  The first-triangle firewall is therefore not a
surviving escape from a **joint** endpoint authentication: it can hide from
the squared parabolic coordinate only by moving the BS implementer a
constant distance.

This sharpens the remaining Iwahori target.  It is enough at the root-lift
stage to authenticate one exact congruence endpoint in the two coordinates
`(R,S^2)`.  Formula `(FPC2)` then returns the half-parabolic `S` with no
spectral matching, functional calculus, conductor estimate, or choice of an
odd square-root exponent.  What remains open is producing that common
`(R,S^2)` endpoint alignment from the inversion and two cubic rows; the
present estimate does not construct it.

