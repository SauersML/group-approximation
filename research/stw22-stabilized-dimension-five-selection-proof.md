---
rg: 2
id: stw22-stabilized-dimension-five-selection-proof
kind: route
title: Apply degree-four Michael selection only to half-slack replication values
target: stw22-dim5-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-half-slack-all-factor-weighted-copy-uniform-s4-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Fix `m>=2` and a positive contraction `a in M` with

```text
m tau_x(supp(a_x))<=1/2             for all x in K.    (AF5-5)
```

The existing stabilization and correction theorem realizes the exact
weighted-copy values as nonempty closed lower-semicontinuous subsets of
one complete `(ell^2)^m`, uniformly over all finite factor types, and
supplies operator-ball recovery. Countable generation makes diffuse fibres
separable-predual.

The universal degree-zero through degree-four results make the values
four-connected and equi-`LC^4` after the fixed-`m` tuple-metric and
ambient-centre conversions. Since `K` is paracompact and `dim(K)<=5`,
Michael with `n=4` gives a continuous exact tuple; operator-ball recovery
places it in `M_1^m`.

For a positive fibre-gap lift `b`, fix `epsilon>0` and arbitrary `m>=2`.
The spectral cut `(b-epsilon)_+` has support trace below `1/(2m)` on an
`m`-dependent neighbourhood. A central cutoff equal to one near the base
point makes it a global half-slack weight without changing its gap class.
The selected `m` copies have orthogonal range positives whose sum is a
positive contraction, so

```text
m sigma([(b-epsilon)_+])<=||sigma||.                   (AF5-6)
```

Let `m->infinity` and then `epsilon->0`. The gap criterion gives (AF5-4).
Type changes require no extra argument because both the graph estimate and
the degreewise minimum modulus are type-free.