---
rg: 2
id: sl3-fold-positive-cross-gram-does-not-select-endpoint
kind: claim
title: Positive cross-Gram rounding is automatic on the SL3 fold and does not select an endpoint
artifacts:
  - research/artifacts/sl3-fold-positive-cross-gram-firewall-2026-08-23.md
distinct_from:
  positive-cross-gram-state-rounds-to-common-pvm: that is a valid polar-gauged common-PVM theorem for an already supplied Gram operator; the present claim proves that its hypotheses are tautological for the binary fold packet and therefore do not imply projective endpoint transfer.
  positive-cross-gram-mass-alone-has-no-holonomy-floor: that leaves an arbitrary relative gauge in an abstract pair of exact packet transports; the present claim shows that even complete same-packet covariance is automatic for `G=PQ`, identifies the missing idempotence/commutator modulus, and computes the canonical local Gram spectrum.
  one-cross-gram-moment-extracts-the-common-polar-gauge: that uses near-full overlap to recover an abstract common polar gauge; the present claim treats the fixed midpoint mass `1/4` and proves that polar-gauge recovery contains no original-coordinate endpoint information.
  sl3-projective-transfer-is-balanced-projection-endpoint-transfer: that identifies the desired global endpoint conclusion; the present claim isolates the principal-angle modulus discarded by positive-Gram polar rounding and gives a finite-matrix sharpness tower.
  finite-swap-conjugate-moments-do-not-fold-arithmetic-double: that realizes each prescribed finite lamp-moment table in some finite quotient; the present claim follows one canonical local tower, computes the full limiting Gram spectrum, and proves that no fixed-density near-isometric Gram sector appears.
  full-arithmetic-bernoulli-projection-orbit-is-free-spherical: that is an exact infinite tracial arithmetic model and is not known to be matricial; the sharpness calibration here consists of exact finite-dimensional representations, but only of the local conjugate-involution group rather than the full arithmetic actor.
---

**ESTABLISHED POLAR-GRAM FIREWALL.**  Let `P,Q` be arbitrary projections in
a finite tracial matrix algebra and put

```text
G=PQ,             H=G^*G=QPQ,             m=||G||_2^2=tr(PQ).
```

For the two binary PVMs `(P,I-P)` and `(Q,I-Q)`, one has identically

```text
PG=GQ=G,                 (I-P)G=G(I-Q)=0.                 (FPG1)
```

Thus the complete packet energy in `(PCR1)` is **zero for every pair of
projections**, while its Gram mass is exactly their overlap `m`.  In
particular, in the balanced projection chart of a hypothetical canonical
microstate of the arithmetic-double swap extension, canonicality of the fold
word gives

```text
m=tr(PQ)=1/4+o(1),
||P-Q||_2^2=1/2+o(1).                                    (FPG2)
```

So `positive-cross-gram-state-rounds-to-common-pvm` applies with fixed mass
and zero intertwining error at the maximally forbidden interior overlap.
Its polar gauge aligns the two range packets but forgets the singular-value
modulus of `PQ`; it cannot imply either endpoint in balanced-projection
transfer.

The exact missing scalar is

```text
d=tr(H-H^2)
 =tr(PQ)-tr(PQPQ)
 =(1/2)||[P,Q]||_2^2.                                    (FPG3)
```

For every `0<epsilon<1`, the top spectral cut

```text
R_epsilon=1_[1-epsilon,1](H)
```

satisfies

```text
R_epsilon<=Q,
tr(R_epsilon)>=m-d/epsilon,
||(P-Q)R_epsilon||_2^2<=epsilon tr(R_epsilon).            (FPG4)
```

Consequently `m>=m_0>0` and `d->0` really do produce a positive-density
near-common fold sector (take `epsilon=sqrt(d)`).  Positive mass and binary
label covariance alone do not.  The native commuting-conjugate-involution
route imposes exactly `d=0`; an arbitrary projective-transfer enemy does not.

In fact `canonical-arithmetic-swap-fold-gram-is-arcsine` determines this
scalar in the actually needed class.  Every hypothetical canonical
microstate sequence of the full arithmetic swap extension satisfies

```text
mu_H =>(1/2)delta_0+(1/2)Arcsine_[0,1],
d->1/16,                                                   (FPG4a)
```

and every spectral window tending to `1` has vanishing trace.  Thus the
canonical character forces the opposite of Gram idempotence; an arithmetic
estimate forcing `d->0` would itself be the non-hyperlinearity
contradiction.

This distinction is sharp in finite matrices with the complete canonical
local moment profile.  Let

```text
Gamma=C_2 * Z=<s,h | s^2=1>,
t=hsh^(-1),
P=(1-s)/2,             Q=hPh^(-1)=(1-t)/2.
```

Choose finite quotients of the residually finite group `Gamma` which are
injective on increasing word balls and use their left regular
representations.  Every fixed nonidentity word then has normalized trace
eventually zero.  The subgroup `<s,t>` is `C_2*C_2`, so the limiting `P,Q`
are free trace-half projections.  The spectral law of `QPQ` is

```text
(1/2) delta_0 + (1/2) Arcsine_[0,1].                     (FPG5)
```

Hence

```text
tr(PQ)->1/4,
tr(PQPQ)->3/16,
d->1/16,
tr(1_[1-epsilon,1](QPQ))->(1/pi)arcsin(sqrt(epsilon)).    (FPG6)
```

For every sequence `epsilon_n->0`, the last top-edge mass tends to zero.
Thus even exact finite representations with all fixed local fold moments
canonical have the automatic mass-`1/4`, zero-label-error Gram but no
fixed-density near-isometric sector.

The finite tower does not refute projective transfer or regular-double fold
collapse because it omits extension by the full approximate arithmetic
actor.  The canonical law `(FPG4a)` is conditional on such a full sequence
existing and therefore also supplies no counterexample.  Together they prove
that a viable use of Lin's package must first obtain an arithmetic same-Gram
estimate contradicting the forced value in `(FPG4a)`, rather than merely
positive Gram mass or PVM-label covariance.
