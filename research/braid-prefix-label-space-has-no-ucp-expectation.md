---
rg: 2
id: braid-prefix-label-space-has-no-ucp-expectation
kind: claim
title: The six-vertex braid prefix label space is neither a fixed-point space nor the range of a ucp expectation
artifacts:
  - research/artifacts/braid-prefix-label-space-ucp-obstruction-2026-08-21.md
distinct_from:
  fixed-chevalley-prefix-grams-give-only-tracial-positivity: that gives approximate label consistency for every fixed word atlas; this computes the first atlas where orthogonal label averaging fails positivity and rules out every ucp projection onto the exact label space.
  chordal-partial-positive-operator-matrices-lift: proper induced subgraphs of the braid hexagon are chordal and lift; the full alternating six-cycle is the first nonchordal repeated-label cell.
---

For the braid `xyx=yxy`, use the six prefix vertices

```text
e, x, xy, xyx=yxy, yx, y.
```

Let `L_br` be the self-adjoint subspace of `M_6` in which the three oriented
`x`-edge entries are equal, the three oriented `y`-edge entries are equal,
and all other entries are free.  Then:

1. `L_br` is not the fixed-point space of any unitary conjugation action;
2. there is no unital completely positive projection from `M_6` onto
   `L_br`;
3. the Hilbert--Schmidt orthogonal label-averaging projection is not even
   positive.

Indeed `L_br` contains every diagonal matrix unit.  Any ucp projection onto
it would fix those projections, hence they lie in its multiplicative domain
and the projection is a diagonal-bimodule Schur multiplier.  But it must fix
the sum of the three `x` matrix units while no individual summand belongs to
`L_br`, an immediate contradiction.  The same argument fences fixed-point
averaging.

For an explicit positivity witness, label the hexagon so the oriented
`x` edges are `(0,1),(2,3),(5,4)` and the `y` edges are
`(1,2),(0,5),(4,3)`.  Orthogonally average entries in each class. Applied to
`vv^*` for `v=(-1,0,1,-1,0,1)`, the output has nonzero entries in rows whose
diagonal is zero, and is therefore not positive (explicitly its quadratic
form on `(-1,-1,-1,1,1,1)` is `-16/3`).

The failure of the natural label average already occurs on the four-prefix
subpath `e,x,xy,xyx`: averaging its two `x` entries sends
`vv^*`, `v=(1,1,0,0)`, to a matrix with lower block
`[[0,1/2],[1/2,0]]`.  Thus negativity occurs before nonchordality; the full
six-cycle is the first nonchordal support of the braid derivation.

Thus the braid cell already blocks the proposed label-class conditional-
expectation repair before it is joined to the quarter-turn atlas.  Any
successful larger averaging construction would have to impose additional
coupled structure, not merely average repeated root labels.
