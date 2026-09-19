---
rg: 2
id: five-fourths-projection-surplus-pays-linear-hs-energy
kind: claim
title: The synchronized V4 five-fourths surplus pays linear Hilbert--Schmidt routing energy
distinct_from:
  full-v4-latent-coordinate-has-an-operator-five-fourths-floor: that constructs the three failure projections and computes their exact total trace; this converts any attempted return into a dimension-free normalized-HS lower bound.
  gram-branching-capacity-with-overlap: that bounds the capacity of supplied partial-isometry ranges; this charges a trace surplus directly to projection-matching error once an exit-capacity bound is available.
  s3-radical-charts-give-linear-local-hs-payment: that charges finite-group type-vector mismatch under three assumed endpoint comparisons; this needs neither a common-coupling argument nor an irreducible-multiplicity estimate after the full V4 packet has been exactified.
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  Let `P` and
`F_1,F_2,F_3` be projections satisfying

```text
sum_i tau(F_i)=(5/4)tau(P).                              (VRE1)
```

For arbitrary unitaries `U_i` and projections `E_i`, put
`Q_i=U_iF_iU_i^*`.  If the exits obey the capacity estimate

```text
sum_i tau(E_i)<=tau(P)+ell,                              (VRE2)
```

then

```text
sum_i ||Q_i-E_i||_2^2 >= (1/4)tau(P)-ell.               (VRE3)
```

In particular, if the `E_i` are pairwise orthogonal subprojections of `P`,
then

```text
sum_i ||U_iF_iU_i^*-E_i||_2^2 >= (1/4)tau(P).           (VRE4)
```

For projections `Q,E`, traciality gives

```text
||Q-E||_2^2
 =tau(Q)+tau(E)-2tau(EQE)
 >= |tau(Q)-tau(E)|.                                    (VRE5)
```

Summing `(VRE5)`, using the triangle inequality on the scalar trace
differences, unitary invariance of trace, and `(VRE1)--(VRE2)` proves
`(VRE3)`.

Apply this to the projections `F_00,F_01,F_11,P_f` of
`full-v4-latent-coordinate-has-an-operator-five-fourths-floor`.  After
fixed-finite-group HS exactification, the identity `(VRE1)` holds up to the
usual vanishing discarded mass.  Therefore any microstate-level construction
which routes the three named failure blocks into exits of total capacity at
most the parent forbidden carrier has a **linear**, dimension-free payment:

```text
E_route >= (1/4)tau(P_f)-o(1).                           (VRE6)
```

This is the sharp local analytic endpoint for the synchronized S3/V4
compiler.  The only remaining local-to-global obligation is to construct the
exit-capacity bound in finite-dimensional microstates without asserting the
same projection routing in the group algebra itself.

