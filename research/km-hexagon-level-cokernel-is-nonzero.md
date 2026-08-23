---
rg: 2
id: km-hexagon-level-cokernel-is-nonzero
kind: claim
title: The product-cycle map has nonzero cokernel at every hexagon twisted level of the (2,4,6) codistance filtration
artifacts:
  - research/artifacts/km-opposition-connectivity-computations-2026-08-23.md
invalidates:
  - km-thick-part-two-connected-via-twisted-surjectivity
distinct_from:
  km-twisted-level-product-cycles-surject: that asserts surjectivity at every twisted level; this establishes its negation at the `G_2` levels by an explicit integral annihilator, refuting it as stated while leaving the grid and `B_2` levels' surjectivity standing.
  km-codistance-filtration-twisted-levels-are-rank-two-pairs: that computes the relative homology of the filtration levels in terms of this cokernel; this decides the cokernel's nonvanishing on the hexagon levels.
---

**THEOREM (established; proof in
`km-hexagon-level-cokernel-proof`).**  Let a twisted level of the
`(2,4,6)` codistance filtration have a `G_2` residue on at least one
side, with `A` the panel-opposition geometry of the split Cayley
hexagon residue (points at maximal distance from the panel line,
classed by their feet; lines the opposite lines).  Whenever the
one-class-deleted incidence graph of `A` is disconnected while the full
graph is connected -- verified by the axiom-checked computations for
`q = 2` (components `[24,24]` already for the full graph) and `q = 3`
(full graph connected, any deletion gives components `[81,81,81]`) --
the map

```text
H_1(A) (x) H_1(B) --> (+)_(matched-class pairs) Z_1(K_(q,q))
```

of `km-codistance-filtration-twisted-levels-are-rank-two-pairs` (d) has
NONZERO cokernel, integrally and rationally.  Hence
`km-twisted-level-product-cycles-surject` is FALSE as stated, in every
computed characteristic, and by the structure theorem the relative
homology `H_3(Z_(<=R+1), Z_(<=R))` is nonzero at every hexagon level.

**Consequences.**  The conditional route to type `F_3` and to
`H^2(Lambda; Z Lambda) = 0` is invalidated; both questions are open
again, and are decided by the connecting maps of the filtration on the
explicit classes dual to the annihilators: some nonzero connecting map
would give `H_2` of the thick part; all connecting maps vanishing on
the degree-three level would revive the vanishing of the group-ring
`H^2` and the death of Ioana--Spaas--Wiersma Corollary D.  Either way
these classes are now the decisive objects of the LP fork.
