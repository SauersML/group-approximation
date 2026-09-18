---
rg: 2
id: titz-witzel-kernel-sofic-via-connected-link-covers
kind: route
title: The Titz--Witzel complex has building links, which are connected, so flat-hitting sparse covers are fully branched and the repaired equivalence makes the simple kernel sofic
target: titz-witzel-kernel-sofic
requires:
  - titz-witzel-flat-hitting-sparse-branched-covers
  - sparse-fully-branched-covers-iff-sofic-with-connected-links
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

**One open prerequisite: `titz-witzel-flat-hitting-sparse-branched-covers`.**
This replaces `titz-witzel-kernel-sofic-via-flat-hitting-covers`, whose
equivalence prerequisite `sparse-fully-branched-covers-iff-sofic-simple-residual`
omits the link hypothesis and, as stated, implies
`titz-witzel-kernel-nonsofic` (see
`finite-branched-covers-force-connected-vertex-links`).

Let `Y = Y_1^2`, `G = pi_1(Y)`, and `K = G^(infinity)`.

1. *Setting.*  By `titz-witzel-simple-kazhdan-cat0-lattices-exist`, `Y` is a
   finite triangle complex whose universal cover `Delta` is a `C~_2`
   building of thickness 3, with `G` acting freely and cocompactly, and `K`
   is infinite simple of finite index.  With the Euclidean metric on the
   chambers, `Y` is piecewise Euclidean with one shape and locally CAT(0).
2. *Links are connected.*  `Delta -> Y` is a covering and a local isometry,
   so every vertex link of `Y` is isomorphic to a vertex link of `Delta`.
   A vertex link of a building of rank 3 is a spherical building of rank 2
   (Tits), that is, a generalized polygon: of type `C_2` (a generalized
   quadrangle, here the incidence graph of `GQ(2,2)`) at special vertices,
   and of type `A_1 x A_1` (a complete bipartite graph, here `K_(3,3)`) at
   the others.  Generalized polygons are connected, with diameter `m` for
   an `m`-gon.  So every vertex link of `Y` is connected.
3. *Flat hitting forces full branching.*  Take the covers `X_k` of
   `titz-witzel-flat-hitting-sparse-branched-covers`, with `beta(X_k) -> 0`
   and condition (H) for some `R_k`.  Let `C` be an unbranched component of
   some `X_k`.  Every vertex of `C` has degree 1, so its star maps
   isomorphically, and `p|_C` is a local homeomorphism.  It is proper, and
   onto by Part 1 of `finite-branched-covers-force-connected-vertex-links`.
   So it is a finite covering of `Y`, and the universal cover of `C` is
   `Delta`.  An apartment of `Delta` is an isometrically embedded Euclidean
   plane.  Its flat `R_k`-disk about a vertex maps locally isometrically into
   `C`, which misses `B`, and this image is the lift through `p` of that disk
   from a vertex of `C`.  That contradicts (H).  So every `X_k` is nonempty
   and fully branched.
4. *Conclusion.*  By 3, item 2 of
   `sparse-fully-branched-covers-iff-sofic-with-connected-links` holds for
   `Y`.  By its 2 => 1, `K` is sofic.

**What the remaining hole really asks.**  By the same equivalence (item 3),
flat hitting is more than needed: it suffices to have sparse branched
covers of `Y_1^2` whose branched components carry a fixed fraction of the
sheets, and that weaker statement is *equivalent* to `titz-witzel-kernel-sofic`.
So a proof of the flat-hitting claim must build something at least as strong
as a sofic approximation of `K`; it cannot be easier than soficity.
