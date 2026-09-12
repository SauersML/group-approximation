---
rg: 2
id: full-hecke-quarter-source-locks-moving-gauges
kind: route
title: Use the B2/B3 quarter source to lock the order-seven moving gauges
target: el20-six-moving-coefficient-square-bridges
requires:
  - b2-b3-pair-full-hecke-four-native-sectors
  - order-seven-moving-cuts-realize-both-affine-profiles
---

Dead route.  Restrict both native rows to the literal common sector

```text
F=Q(1+r)(1+t)/4,
```

whose rank is `rank(Q)/4`, and transport `F` through the seven moving
cuts.  The hoped inference was that the two independent sign flips on the
full Hecke source would remove the moving-frame coboundary and force each
stage bridge to have reservoir factor one.

`full-hecke-quarter-source-does-not-lock-moving-gauges` gives an exact
finite packet with the sharp four-sector ranks, a literal positive common
quarter source, both exact affine selector profiles, zero moving boundary,
and exact seventh powers, while the two reservoir involutions have positive
fractions `1/2` and `5/6` and vary nontrivially around the seven stages.
The B2/B3 rows act only on the finite sign factor and do not compare it with
the moving reservoir frame.

Thus the quarter source pays mass but not occurrence typing.  A surviving
route still needs an ordinary mixed EL20 relation which places a Hecke sign
flip and a moving coefficient bridge on the same occurrence, or the
independently ungauged bridges required by `(ESB2)--(ESB3)`.
