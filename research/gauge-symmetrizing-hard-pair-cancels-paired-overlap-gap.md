---
rg: 2
id: gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap
kind: claim
title: Gauge symmetrization of the hard pair cancels the paired-frame overlap gap
distinct_from:
  gauge-doubling-gives-selector-flip-symmetries: that proves simultaneous share flips preserve every logical BCS word and exact solution; this shows why forgetting the resulting private orientation also forgets the paired-frame detector.
  paired-frame-forbidden-scalar-overlap-gap: that proves a fixed scalar gap on the oriented `101` carrier; this proves the gap vanishes after adjoining its equally weighted `011` gauge partner.
  paired-frame-hard-characters-form-forced-two-cycle: that classifies the character permutation of every finite edge; this computes the induced cancellation of the full commutant/Reynolds checksum.
---

Let `alpha` be the support-packet automorphism interchanging the first two
central coordinates, let

```text
h=101,       h'=011=alpha(h),
V_-=alpha^*V_+,                                           (GHC1)
```

The fixed central subgroup is

```text
Z^alpha=<J z_e,z_f>,                                      (GHC1a)
```

and `h,h'` have the same restriction to it.  Thus `Jz_e` is the
flip-invariant logical sign while the distinction between `h,h'` is a
private orientation; forgetting that orientation identifies exactly the two
sectors in `(GHC1)`.

and write

```text
C_+(k)=End_B(S_k tensor V_+),
C_-(k)=End_B(S_k tensor V_-).                            (GHC2)
```

Then pullback by `alpha` gives canonical algebra isomorphisms

```text
C_-(h') isomorphic C_+(h),
C_-(h)  isomorphic C_+(h').                              (GHC3)
```

Consequently, for every multiplicity `m`,

```text
C_+(h)^m directSum C_+(h')^m
  isomorphic
C_-(h)^m directSum C_-(h')^m.                            (GHC4)
```

The corresponding direct-sum Reynolds projections are unitarily conjugate
and have full scalar overlap.  Thus the fixed `1/98` oriented gap from
`paired-frame-forbidden-scalar-overlap-gap` disappears after equal-weight
symmetrization over the hard two-cycle.

This applies directly to the naive gauge-ownership repair.  In the lifted
coordinates one may preserve the logical product while regarding `h,h'` as
the two private gauge orientations.  Exact gauge-orbit covariantization gives
them equal multiplicity, so a checksum conditioned only on the logical
product admits the stationary counterflow `(GHC4)`.  Gauge doubling therefore
solves semantic covariance and exact completeness, but it cannot replace a
one-sided orientation label.  A successful derived bridge must retain which
hard orientation entered the actuator, or couple the flip to an infinite
coordinate which does not return.
