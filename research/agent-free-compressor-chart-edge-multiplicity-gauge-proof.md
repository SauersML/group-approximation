---
rg: 2
id: agent-free-compressor-chart-edge-multiplicity-gauge-proof
kind: route
title: Compute the commutant gauge and transport one spectral projection
target: agent-free-compressor-chart-edge-has-multiplicity-gauge
requires: []
---

The commutant of `M_r(C) tensor I_m` is `I_r tensor M_m(C)`. Hence the ratio
of any two chart-edge implementers lies in `I_r tensor U(m)`, proving
`(MCG2)`. This group acts transitively on multiplicity projections of any
fixed rank and realizes every possible intersection dimension allowed by
linear algebra, so chart relations alone cannot fix a prefix incidence.

For involutions `s,s'`, substitute `C=(1+s)/2` and `C'=(1+s')/2` and calculate

```text
TCT^*-C'=(TsT^*-s')/2.
```

This proves `(MCG4)` and the sufficiency of the single mixed conjugacy at the
representation level.
