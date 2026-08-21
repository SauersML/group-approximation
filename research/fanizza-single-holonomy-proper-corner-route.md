---
rg: 2
id: fanizza-single-holonomy-proper-corner-route
kind: route
title: Attach one proper-corner return to the unique native Fanizza holonomy
target: non-hyperlinear-group
requires:
  - fanizza-native-additive-incidence-is-one-triangle
  - gauge-doubling-gives-selector-flip-symmetries
  - unicyclic-packet-atlas-concentrates-incidence-in-one-holonomy
  - pauli-quarter-holonomy-is-balanced-derived-reset
  - group-algebra-mark-reverse-kleene-collapse
  - single-triangle-trace-cyclic-return-cell
---

Keep every native involution, group, conjugacy, and commutation equation
multiplicative.  Gauge-double the four remaining Boolean contexts.  Normalize
the attached leaf and two edges of the unique triangle by the spanning-tree
theorem.  All exact incidence freedom is then one commutant holonomy on the
last binary separator.

Use the two native quarter carriers as the finite holonomy packet.  Their
reflections generate exact `D_8`; the derived negative central cut has trace
`1/8` and is a rational group-algebra projection.  The final cell should make
this one chord holonomy the defect of a Toeplitz/trace-cyclic return.  Exact
halting completeness may choose the chord unitary on countably infinite
multiplicity and absorb the proper corner.  Finite matrices must pay the
cyclic-trace defect, causing the chosen rational group-algebra mark to
collapse on the nonhalting side.  Reverse Kleene then supplies the
nonhyperlinear group.

The route removes three former global requirements:

- no arbitrary context-atlas cycle basis remains;
- no literal group-word realization of the D8 reflections is needed; and
- no tracial extension of the exact witness is required.

The load-bearing theorem is deliberately isolated as
`single-triangle-trace-cyclic-return-cell`.  A finite graph-of-groups
holonomy is insufficient, and merely naming the D8 projection as a
proper-corner defect would assume the missing finite-matrix decoder.
