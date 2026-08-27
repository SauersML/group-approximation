---
rg: 2
id: central-third-root-no-ce-sector-forces-nonhyperlinear
kind: claim
title: A nonempty central third-root sector with no CE trace forces nonhyperlinearity
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  thom-central-corner-criterion: that characterizes hyperlinearity using every character of an arbitrary central subgroup; this is the precise one-character contradiction consumed by the qutrit compiler.
  central-sign-bcs-energy-decoder-implies-nonhyperlinear: that uses approximate matrix energy on a central involution corner; this uses exact exclusion of every CE trace in one order-three character sector.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that requires a unital BCS algebra map into the canonical group-algebra corner; this only requires that the sector admit no CE trace at all.
---

Let `Gamma` contain a central element `J` with `J^3=1`.  Suppose:

1. some tracial representation sends `J` to `omega I`, where
   `omega=exp(2 pi i/3)`; and
2. no Connes-embeddable tracial representation sends `J` to `omega I`.

Then `Gamma` is nonhyperlinear.

The first hypothesis proves that `J` has exact order three.  Hence in the
canonical group factor the central spectral projection

```text
e_omega=(1+omega^2 J+omega J^2)/3                    (C3C1)
```

is nonzero and has canonical trace `1/3`.  Hyperlinearity would make the
canonical group factor Connes embeddable.  Normalizing its trace on the
corner `(C3C1)` would then give a CE trace in which `J=omega`, contrary to
hypothesis 2.

