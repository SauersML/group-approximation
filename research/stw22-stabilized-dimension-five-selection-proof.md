---
rg: 2
id: stw22-stabilized-dimension-five-selection-proof
kind: route
title: Apply degree-four half-slack selection in the stabilized L2 field
target: stw22-dim5-factor-bundles-have-uniform-traces
requires:
  - stw22-half-slack-all-factor-weighted-copy-uniform-s4-fillings
  - stw22-dim4-factor-bundles-have-uniform-traces
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim5-factor-bundle-breakthrough-2026-08-31.md
---

Fix `m>=2` and a positive contraction `a in M` with
`m tau_x(supp(a_x))<=1/2` everywhere.  Stabilization puts the exact
weighted-copy values in one complete `(ell^2)^m`; the factor-uniform
correction lemma makes the multifunction lower semicontinuous with
nonempty closed values.  The degree-zero through degree-four theorems make
the values globally four-connected and uniformly equi-`LC^4`.  After the
standard ambient-centre and fixed-`m` tuple-metric conversions, Michael's
theorem with `n=4` applies over `dim(K)<=5`.  Operator-ball recovery returns
the selected exact tuple to `M`.

For a positive fibre-gap class, take a spectral cut and a central cutoff
supported where its support trace is below `1/(2m)`.  The selected `m`
orthogonal copies bound every bounded positive gap trace by its norm divided
by `m`.  Let `m` tend to infinity through integers at least two and then
remove the spectral cut.  The exact gap criterion proves the claim.

