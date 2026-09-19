---
rg: 2
id: atlas-one-forward-c3-has-no-standard-gl6-completion
kind: claim
title: One forward central-C3 context already excludes every standard GL6(2) chart completion
artifacts:
  - experiments/atlas_a4_gl6_bordered_forward_search.py
  - experiments/atlas_a4_gl6_forward_instance.py
  - experiments/atlas_a4_gl6_forward_sat.py
  - research/artifacts/atlas-a4-one-forward-gl6-unsat.json
distinct_from:
  atlas-central-c3-directed-gl5-classification: that exhausts GL5 and shows any forward context excludes its 216 core-plus-collision points; this performs a direct exact Boolean classification of all standard GL6 relative frames for one fixed forward context.
  atlas-a4-rank-three-core-commutant-collapse: that was a false dimension-free complex Hilbert-space claim without central contexts; this finite-field result adds one forward context and only classifies a specific six-dimensional F2-linear model.
---

Embed each chart `A8=GL_4(F2)` in `GL_6(F2)` as

```text
g |-> diag(g,I_2).
```

Fix the forward central constraint whose first-chart central label and
second-chart involution have hexadecimal matrices

```text
z = 01000000000100000000010100000100,
b = 01010000000100000000010000000001.                  (A4-GL6-FWD)
```

There is no `R in GL_6(F2)` for which the two charts `j_1` and
`j_2=Ad(R)j_1` simultaneously satisfy

```text
the fourteen rank-three core pair-cubes,
q_19243(j_1,j_2)=1,
(j_1(z)j_2(b))^3=1.                                   (A4-GL6-UNSAT)
```

The conclusion is stronger than commutant collapse in this one finite model:
the exact solution fiber is empty.  In particular there is no escaping frame,
and no commuting frame either.

This is an exhaustive finite-rank theorem, not a dimension-independent
Hilbert--Schmidt estimate.  It shows that adding a trivial two-dimensional
padding module does not repair the forward obstruction found in GL5.  A
positive full-packet proof still has to explain why the same obstruction
persists for arbitrary complex multiplicity; an exact finite tracial factor
can satisfy even the full packet, so such an explanation must use matrix
approximability rather than ordinary group-word consequence alone.
