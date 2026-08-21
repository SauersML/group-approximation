---
rg: 2
id: symmetric-selector-packet-proves-derived-reset-bridge
kind: route
title: Combine gauge covariance, the primitive residual packet, and the balanced four-point restriction
target: derived-lifted-gauge-reset-spin-bridge
requires:
  - gauge-doubling-gives-selector-flip-symmetries
  - symmetric-selector-schur-residual-packet
  - symmetric-selector-rank-swap-has-balanced-restriction
---

Gauge doubling makes every reset translation flip two private shares and
therefore fixes every logical product, every lifted BCS constraint, and the
native signal.  The finite direct-sum gauge orbit gives exact covariant marked
completeness.

For each fixed arity-four predicate packet, use the symmetric selector power.
Its selected primitive type contains every rank-fifteen residual sector once,
and its twisted symmetric action implements all fixed residual congruences.
The reset translation is an explicit commutator, fixes the common diagonal
residual pointwise, and changes the selector signs by the required affine
gauge rule.

Install the two complementary four-point pairs inside the signed-permutation
subgroup already present on the gauge orbit.  By
`symmetric-selector-rank-swap-has-balanced-restriction`, the two reset signs
each contain four rank-sixteen spin packets and restrict to the common
rank-fifteen edge with the same multiplicity.  The missing hyperbolic pair is
therefore replaced rather than tensored on, so the normalized packet scale is
unchanged.

All operations belong to one fixed finite group.  Exactify its complete table
and use the primitive character projection for the selected type.  Standard
finite-group flexible Hilbert--Schmidt stability and polar alignment of a
fixed finite set of overlap blocks give `O(sqrt(E))` loss with a constant
depending only on this finite incidence.  No ambient multiplicity, selector
sector, or computation depth enters the constant.  This proves all five
clauses of `derived-lifted-gauge-reset-spin-bridge`.

