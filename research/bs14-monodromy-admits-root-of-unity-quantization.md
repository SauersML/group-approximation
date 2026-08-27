---
rg: 2
id: bs14-monodromy-admits-root-of-unity-quantization
kind: claim
title: Scalar BS(1,4) monodromies can be quantized to Mth roots at pi/M Hilbert--Schmidt cost
artifacts:
  - research/artifacts/bs14-full-commutant-preconditioning-2026-08-22.md
  - experiments/bs14_monodromy_quantization_check.py
distinct_from:
  bs14-unitary-representations-are-periodic-cycle-packets: that exposes the arbitrary scalar return phases in every exact packet; this rounds all of those phases while preserving the exact BS relation and the matrix dimension.
  bs14-long-cycles-admit-bounded-period-shadowing: that truncates the discrete fourth-power orbit length and leaves continuous packet monodromy; this quantizes the continuous return coordinate while leaving the base unitary fixed.
  bs14-exact-representation-variety-is-hs-locally-rigid: that aligns two nearby exact BS skeletons; this constructs a nearby finite-order monodromy skeleton from one exact skeleton.
---

Let `R,S in U(d)` satisfy

```text
R S R^(-1)=S^4.                                      (BMQ1)
```

For every integer `M>=2` there is `R_M in U(d)` such that

```text
R_M S R_M^(-1)=S^4,
||R-R_M||_2^2 <= pi^2/M^2,                            (BMQ2)
```

and every scalar packet monodromy of `(R_M,S)` is an `M`th root of unity.
The base unitary `S`, its spectral projections, all fourth-power orbit
lengths, and the ambient matrix dimension are unchanged.

More explicitly, in the scalar packet normal form attached to an orbit of
length `m`, write `R^m=v`.  The corresponding packet for `R_M` has
`R_M^m=w`, where `w^M=1`.  Thus if all fourth-power orbit lengths of `S` are
at most `K`, then on the full orbit block of the base commutant `{S}'`,

```text
Ad(R_M)^(mM)=1,                    m<=K.               (BMQ3)
```

This includes every off-diagonal matrix direction between equal-orbit
multiplicity packets; the continuous monodromy ratios have become finite
cyclic data.
