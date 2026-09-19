---
rg: 2
id: stw79-rational-index-criterion-proof
kind: route
title: Rationalize the quotient K-zero group while retaining every nonzero index
target: stw79-rational-stabilization-removes-kzero-torsion
requires:
  - stw79-total-order-af-index-dr-dichotomy
artifacts:
  - research/artifacts/stw79-rational-index-criterion-2026-09-05.md
---

Tensoring the extension by `Q` preserves exactness and essentiality.
The new ideal coefficient `B tensor Q` is simple unital AF and has
totally ordered `K_0(B) tensor_Z Q`; the quotient has finite decomposition
rank and rational-vector-space K-zero. Matrix-stage direct limits give
the rationalized boundary `delta tensor id_Q`. Since `K_0(B)` is
torsion-free, this map vanishes exactly when `delta` does. Apply the
prerequisite to obtain the formula.

Finite decomposition rank of `E tensor Q` implies its quasidiagonality,
which passes to the canonical copy of `E`. Quasidiagonality implies
stable finiteness. Finally, stable finiteness forces `delta=0` by the
positive-projection argument of the prerequisite; that direction never
used torsion-freeness of the quotient K-zero group. These implications
give the stated equivalences without a rational descent assertion for
decomposition rank.
