---
rg: 2
id: bs14-exact-representation-variety-is-hs-locally-rigid
kind: claim
title: Close exact BS(1,4) representations are near-conjugate with a dimension-free modulus
distinct_from:
  skeleton-relative-hs-stability-for-sl2: that is the gluing claim consuming this as its first leg; this is the local rigidity of one skeleton's exact variety, with no gluing and no second swap.
  approximate-doubling-invariant-joint-measure-is-atomic: that is the joint coupled-parabolic target; this concerns a single parabolic skeleton's exact representations only.
---

There is a modulus `f(eps) -> 0`, independent of dimension, such that
any two EXACT finite-dimensional unitary representations `(V, W)` and
`(V', W')` of `BS(1,4)` on the same space with
`||V - V'||_2, ||W - W'||_2 <= eps` (normalized HS) admit a unitary
`u` with

```text
|| u V' u* - V ||_2  <=  f(eps),
|| u W' u* - W ||_2  <=  f(eps).
```

Near-conjugacy, not small-conjugator: exactly what the skeleton
gluing consumes.  The proof (route below) runs on the semisimple
classification — finite-dimensional `BS(1,4)`-irreducibles are pairs
(odd `x4`-cycle `C`, monodromy phase `omega`), of dimension the cycle
length — via multiscale spectral clustering: invariant multisets are
DIScontinuous under perturbation (cycles of different odd orders and
lengths collide), but every discontinuity reorganizes within a
cluster and never costs more than the cluster scale, so the transport
distance of representations (unlike that of invariants) is
continuous.  Expected modulus `f(eps) ~ eps^(1/2)` up to logarithms.

The same scheme should extend to the full solenoid group
`Z[1/2] rtimes_4 Z` (joint solenoid spectrum in place of the circle,
same clustering and transport), which is the form the skeleton route
uses for the whole tower at once; the extension is bookkeeping over
the same mechanism and is recorded as the follow-on obligation.

## Attempts

- Established by the proof route below (multiscale clustering,
  Davis--Kahan in Hilbert--Schmidt form, monodromy transport).  The
  one point demanding care is the scale-selection pigeonhole, which
  is what makes every constant dimension-free.
