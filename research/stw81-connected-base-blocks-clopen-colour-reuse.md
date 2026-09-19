---
rg: 2
id: stw81-connected-base-blocks-clopen-colour-reuse
kind: claim
title: A connected one-dimensional base blocks the clopen colour-reuse proof
distinct_from:
  stw81-zero-dim-simple-fields-obey-trichotomy: that proves an exact fibrewise formula by approximating the zero-dimensional base with finite-dimensional commutative algebras; this proves that mechanism stops sharply beyond zero dimension.
  stw81-one-dim-elementary-oinfty-fields-have-dim-one: that overcomes the lost clopen approximation using continuous-trace dimension or O-infinity-absorption; this isolates why extra fibre regularity is needed.
artifacts:
  - research/artifacts/stw81-one-dimensional-field-audit-2026-08-30.md
---

Let `X` be a connected compact Hausdorff space with more than one point.
Then every finite-dimensional C-star subalgebra of `C(X)` is either zero
or the constants.  Consequently `C(X)` cannot be locally approximated by
finite-dimensional commutative subalgebras, and for every nonzero C-star
algebra `B`, the subalgebras

`F tensor B`,  `F subset C(X)` finite dimensional,

cannot approximate `C(X) tensor B`.

Thus the proof of
`stw81-zero-dim-simple-fields-obey-trichotomy` cannot extend to a
connected one-dimensional base: its zero-cost colour reuse is equivalent
to clopen finite-dimensional approximation of the base.  A
one-dimensional base already needs two topological colours; combining
those naively with a one-dimensional fibre gives the general tensor bound
of three rather than the desired bound of one.  The elementary and
O-infinity-stable cases evade this respectively through the
continuous-trace calculation and absorption, not through clopen reuse.
