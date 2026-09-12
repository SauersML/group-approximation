---
rg: 2
id: reverse-mixed-root-positive-hecke-return-proof
kind: route
title: Bracket the actual reverse root with two positive signed-Hecke generators and type the outputs
target: reverse-mixed-root-has-two-positive-hecke-commutator-returns
requires:
  - actual-mixed-complement-returns-reverse-root
  - signed-hecke-normalizer-has-eight-external-root-returns
  - eight-external-returns-have-no-whitehead-gauge-lock
---

In matrix-root coordinates, `(ERN1)` contains the positive arrows `6->7`
and `9->2`, hence the positive-character roots `x_76(1)` and `x_29(1)`.
The composable paths

```text
(9,7)(7,6)=(9,6),             (2,9)(9,7)=(2,7)
```

and the Steinberg commutator relation prove `(RMR3)`.  Characteristic two
makes every displayed root an involution, so right multiplication by the
positive root gives `(RMR4)`.  The positions `(9,6)` and `(2,7)` are in the
external signed-normalizer list `(EWO1)`, proving the signed-source return.

The row-one and row-two fixed-root classification `(EWO3)` is exactly
`x_96` and `x_27`, respectively.  The proof of that claim supplies the
finite moving-chart `S_3` witness and shows that these fixed roots are
disjoint spectators.  It realizes the new commutator outputs by assigning
their returned gauges to the corresponding spectator factors, while the
active Whitehead/opposite gauges remain distinct reflections.  Therefore
the new words return `Q` but do not give a native same-reservoir gauge
identity.
