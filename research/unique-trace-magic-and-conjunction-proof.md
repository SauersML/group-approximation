---
rg: 2
id: unique-trace-magic-and-conjunction-proof
kind: route
title: Append a uniquely tracial magic-square AND block to a separated BCS
target: matrix-conj-forces-unsafe-support
requires:
  - mipstar-bcs-tracial-nonru-exists
---

Use the magic-square parity equations to eliminate five entries.  The last
column equation and the remaining row commutation turn the four generators
into two commuting Pauli pairs, so the universal algebra is `M_4(C)`.  Add
the graph-of-AND context; its new observable is the polynomial `(UTC5)`, so
the algebra and its unique trace do not change.  The unique trace gives
positive mass to all four graph atoms, whose affine hull contains the
forbidden point `110`.  Finally take the disjoint union with the established
tracial non-`R^U` BCS.  Restriction preserves non-`R^U` soundness, while every
trace restricts to the unique unsafe trace on the matrix block.
