---
rg: 2
id: fanizza-single-holonomy-proper-corner-route
kind: route
title: Dead route - the prescribed Pauli guard removes the apparent native holonomy
target: non-hyperlinear-group
requires:
  - fanizza-native-additive-incidence-is-one-triangle
  - gauge-doubling-gives-selector-flip-symmetries
  - unicyclic-packet-atlas-concentrates-incidence-in-one-holonomy
  - pauli-quarter-holonomy-is-balanced-derived-reset
  - group-algebra-mark-reverse-kleene-collapse
  - single-triangle-trace-cyclic-return-cell
---

DEAD.  This route treated the last C18 triple as an independent selector
packet.  In the native presentation its product is identically one, so C18
reduces to the first-triple projection recurrence and the triangle chord is
absent.  See `pauli-guard-collapses-c18-to-three-bit-recurrence` and the live
replacement `fanizza-native-join-tree-groupification-route`.

The discussion below is retained as a warning: it would be relevant to a
different source with a genuine unicyclic prescribed-word atlas, but it is
not a load-bearing Fanizza route.

Keep every native involution, group, conjugacy, and commutation equation
multiplicative.  Gauge-double the four remaining Boolean contexts.  Normalize
the attached leaf and two edges of the unique triangle by the spanning-tree
theorem.  All exact incidence freedom is then one commutant holonomy on the
last binary separator.

The bare Boolean triangle is classically flat: every assignment of its three
separator signs extends to all four contexts.  Therefore the D8 charge cannot
be inferred from cycle topology or marginal compatibility.  It must be tied
to the fact that the three separator observables are the prescribed machine
words in the native Fanizza algebra.  Replacing them by freely chosen signs
would destroy the only possible obstruction.

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
