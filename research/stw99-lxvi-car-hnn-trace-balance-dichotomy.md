---
rg: 2
id: stw99-lxvi-car-hnn-trace-balance-dichotomy
kind: claim
title: Every CAR HNN covariance is either trace balanced or makes the ambient unit properly infinite
distinct_from:
  stw99-lxvi-finite-seed-has-no-quasitrace: that proves abstractly that a completed simple LXVI seed has no quasitrace; this detects infiniteness directly from one trace-mismatched HNN edge before simplicity or the first unstable amplification is considered.
  stw99-lxvi-tracial-free-constructions-are-stably-finite: that treats trace-preserving reduced free products and crossed products; this gives the complementary HNN dichotomy and proves that the obvious non-trace-preserving escape makes the unit infinite immediately.
  stw99-lxvi-k0-dyadic-divisibility-obstruction: that tests whether a finite corner can contain a coherent CAR tower; this assumes the CAR copy already exists and constrains equivalences between its projections in the ambient algebra.
artifacts:
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

Let `D=M_(2^infinity)` with its unique trace `tau_D`, and let `D subset A`
be a unital inclusion.  If positive contractions `a,b in D` are unitarily
conjugate in `A` but

```text
tau_D(a)!=tau_D(b),                                           (1)
```

then `1_A` is properly infinite.  Consequently, for an arbitrary unital
C*-algebra `C` and unital embeddings `theta_0,theta_1:C->D`, a unitary
`u in A` satisfying

```text
u theta_0(c) u*=theta_1(c)                    (c in C).         (2)
```

can coexist with a finite unit only if

```text
tau_D after theta_0=tau_D after theta_1.                         (3)
```

Equivalently, any trace-mismatched CAR HNN covariance makes the ambient unit
properly infinite.  No projections in `C`, simplicity, expectation,
exactness, or nuclearity are needed.

The projectionless boundary is nonvacuous.  There are two explicit unital
embeddings

```text
theta_0,theta_1:C([0,1])->D
```

which agree on every projection of `C([0,1])` but induce different traces.
For these embeddings, every unital ambient algebra containing a covariance
unitary has properly infinite unit.

For a finite-dimensional edge algebra `C`, this gives an exact dichotomy for
the standard HNN constructions:

1. if the two edge traces differ, the unit of both the full and reduced HNN
   extensions is infinite;
2. if the edge traces agree, the reduced HNN extension formed with the
   trace-preserving expectations onto the two edge images has a faithful
   tracial state and is stably finite.  The full HNN extension has a tracial
   state; if it is simple, it coincides with its reduced quotient and is
   stably finite.

Thus neither the trace-balanced nor the trace-mismatched finite-dimensional
HNN construction can produce the simple finite but non-stably-finite
CAR-containing seed equivalent to Problem LXVI.  More generally, allowing a
projectionless edge does not open a non-trace-preserving route: spectral
cutdowns and Cuntz comparison in CAR recover the obstruction.  A viable
HNN-type construction with finite unit must be trace balanced on the entire
edge algebra and must leave the standard faithfully tracial reduced
framework by some other mechanism.
