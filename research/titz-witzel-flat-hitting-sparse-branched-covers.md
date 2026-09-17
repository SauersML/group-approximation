---
rg: 2
id: titz-witzel-flat-hitting-sparse-branched-covers
kind: claim
title: The smallest Titz--Witzel complex has flat-hitting branched covers of arbitrarily small branching mass
distinct_from:
  titz-witzel-kernel-sofic: that is soficity of pi_1(Y_1^2); this is a purely combinatorial existence statement about finite branched covers of Y_1^2, and it implies nothing about soficity unless the covers' hyperbolic fundamental groups are sofic.
  radu-square-complex-flat-hitting-sparse-branched-covers: that is the same statement for Radu's square complex S_R, where cubulation makes it sufficient on its own; this is the triangle-complex version on the exotic C2-tilde building.
  titz-witzel-sparse-defect-needs-dense-generator-surgery: that shows the monodromy of any marked model is far from every exact finite model; the covers here are not edits of exact models, so that obstruction does not apply.
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
---

**OPEN.**  Let `Y = Y_1^2`, the Titz Mite--Witzel `C~_2` triangle complex
with 7 vertices, 45 edges and 45 triangles.  Its links are:
* at `v` and `w`, the incidence graph of `GQ(2,2)`, with edge angle `pi/4`;
* at `u_1..u_5`, the graph `K_(3,3)`, with edge angle `pi/2`.

The claim: for every `eta > 0` there is a finite branched cover `X -> Y` in
the sense of `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`
satisfying three conditions.

1. `beta(X) < eta`.
2. **(G)** Every branch vertex has link girth at least 10 over `v, w`, and
   at least 6 over the `u_i`.
3. **(H)** For some `R`, every combinatorial flat `R`-disk of the building,
   lifted to `X` from any vertex, meets a branch vertex.

## Consequences

* With `titz-witzel-flat-hitting-branched-cover-groups-are-sofic`, it gives
  `titz-witzel-kernel-sofic`.  The covers have hyperbolic `pi_1`, by
  `flat-hitting-branched-covers-have-hyperbolic-pi1`.
* With `titz-witzel-kernel-nonsofic`, it gives `nonsofic-hyperbolic-group`.
  Some cover in the sequence must then have nonsofic, hyperbolic `pi_1`.

So whichever way the soficity of the kernel goes, this combinatorial
statement converts the answer into a statement about hyperbolic groups.

## Necessary conditions and non-obstructions

* **Sparse branching is forced by soficity.**  By part 2 of the reduction,
  soficity of `pi_1(Y)` gives branched covers with `beta -> 0`.  Only (G)
  and (H) are extra.
* **No unbranched version.**  With `beta = 0`, every component of `X` is a
  genuine finite cover of `Y`, so it has degree at most 2, because the
  finite residual has index 2.  Such a cover contains flats, so (H) fails.
* **Density.**  (H) forces `B` to be `R`-dense, so `beta >~ c / R^2` by
  averaging over disks.  Condition 1 then needs `R -> infinity`.  Every flat
  `R`-disk has about `R^2` vertices, so counting gives no contradiction.
* **Curvature and L2-invariants.**  `chi(X) = 7N - sum_b (d_b - 1) > 0` for
  small `beta`.  This is compatible with a torsion-free hyperbolic 2-complex
  group, so there is no L2-Betti obstruction.
