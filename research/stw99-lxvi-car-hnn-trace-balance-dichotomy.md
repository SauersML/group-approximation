---
rg: 2
id: stw99-lxvi-car-hnn-trace-balance-dichotomy
kind: claim
title: CAR HNN covariance is either trace balanced or makes the ambient unit infinite
distinct_from:
  stw99-lxvi-finite-seed-has-no-quasitrace: that proves abstractly that a completed simple LXVI seed has no quasitrace; this detects infiniteness directly from one trace-mismatched HNN edge before simplicity or the first unstable amplification is considered.
  stw99-lxvi-tracial-free-constructions-are-stably-finite: that treats trace-preserving reduced free products and crossed products; this gives the complementary HNN dichotomy and proves that the obvious non-trace-preserving escape makes the unit infinite immediately.
  stw99-lxvi-k0-dyadic-divisibility-obstruction: that tests whether a finite corner can contain a coherent CAR tower; this assumes the CAR copy already exists and constrains equivalences between its projections in the ambient algebra.
artifacts:
  - research/artifacts/stw99-lxvi-coherent-car-no-go-audit-2026-08-30.md
---

Let `D=M_(2^infinity)` with its unique trace `tau_D`, and let `D subset A`
be a unital inclusion.  If `1_A` is finite, then ambient Murray--von Neumann
equivalence of projections from `D` preserves their CAR trace:

```text
p,q in Proj(D), p equivalent_A q  =>  tau_D(p)=tau_D(q).       (1)
```

Consequently, let `C` be a unital real-rank-zero C*-algebra, let
`theta_0,theta_1:C->D` be unital embeddings, and suppose a unitary `u in A`
satisfies

```text
u theta_0(c) u*=theta_1(c)                    (c in C).         (2)
```

If `1_A` is finite, then

```text
tau_D after theta_0=tau_D after theta_1.                         (3)
```

Equivalently, if the two induced traces differ, every unital ambient
C*-algebra satisfying the HNN covariance relation `(2)` has infinite unit.
No simplicity, expectation, exactness, or nuclearity is needed.

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
CAR-containing seed equivalent to Problem LXVI.  A viable HNN-type route
must use an edge whose trace mismatch is invisible on projections (hence not
real rank zero), or a nonstandard simple envelope which is neither the
trace-preserving reduced construction nor a finite ambient realization of a
projection-mismatched covariance.
