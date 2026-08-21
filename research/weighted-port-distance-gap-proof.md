---
rg: 2
id: weighted-port-distance-gap-proof
kind: route
title: Interpolate a zero-one cut across the port distance
target: weighted-equality-gap-forbids-separated-port-mass
requires: []
---

Define

```text
f(v)=min(1, dist(v,Q_0)/R).                                    (1)
```

Then `f=0` on `Q_0`, `f=1` on `Q_1`, and every graph edge changes `f` by at
most `1/R`.  With the standard reversible normalization
`sum_{uv}c_uv=O(1)`, this gives

```text
E(f)<=C_0/R^2.                                                  (2)
```

Because `(WEG1)` puts mass at least `c` at each endpoint value, the variance
of `f` is at least a universal positive multiple of `c` (and at least
`c^2` under the weakest convention).  The Rayleigh quotient
`E(f)/Var_mu(f)` proves `(WEG2)`, after absorbing the harmless normalization
choice into `C`.

For a reflection-valued equality test, the same scalar test function can be
implemented by two fixed macroscopically separated reflections and a gradual
rotation along `(1)`.  Thus the spectral estimate corresponds to an actual
coherent-drift strategy, not only a formal weakness of Poincare's proof.

