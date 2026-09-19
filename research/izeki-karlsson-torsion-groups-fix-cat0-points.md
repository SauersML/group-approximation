---
rg: 2
id: izeki-karlsson-torsion-groups-fix-cat0-points
kind: claim
title: A finitely generated torsion group of subexponential growth, or a finitely generated weakly Liouville simple group, fixes a point in every isometric action on a finite-dimensional complete CAT(0) space
distinct_from:
  two-dim-cat0-product-groups-are-torsion-locally-finite: that uses the Norin-Osajda-Przytycki fixed point theorem for 2-dimensional triangle complexes, with finite stabilizers in the acting group; this imports the Izeki-Karlsson fixed point theorem for complete CAT(0) spaces of any finite dimension, with no properness, cocompactness or complex structure, but only for torsion groups of subexponential growth and weakly Liouville simple groups.
  hyperbolic-kac-moody-lattices-are-torsion-locally-finite: that uses Haettel-Osajda for buildings with word-hyperbolic Weyl group and covers every finitely generated torsion group; this covers every finite-dimensional complete CAT(0) space but only torsion groups of subexponential growth.
  haagerup-cut-out-completions-force-haagerup-quotients: its proof lists Izeki-Karlsson as an unquoted standard input; this is the verbatim import.
---

**ESTABLISHED by citation** (`izeki-karlsson-torsion-groups-fix-cat0-points-citation`).

Let `Y` be a complete CAT(0) space of finite dimension, in the sense of
Izeki-Karlsson: the greatest `D` such that some barycentric simplex on points
`x_0, ..., x_D` is non-degenerate. Let a group `Λ` act on `Y` by isometries,
with no further assumption on the action or on `Y`.

1. (IK Corollary 4.) If `Λ` is a finitely generated torsion group of
   subexponential growth, then `Λ` has a global fixed point in `Y`.
2. (IK Corollary 5.) If `Λ` is a finitely generated simple group that is weakly
   Liouville, then `Λ` has a global fixed point in `Y`. By IK, every finitely
   generated group of subexponential growth is weakly Liouville (Avez).

`Y` need not be proper, and need not be a CAT(0) complex. The action need not be
proper, cocompact or non-elementary. Both items are quoted verbatim in the
citation route.
