---
rg: 2
id: titz-witzel-flat-hitting-branched-cover-groups-are-sofic
kind: claim
title: Fundamental groups of flat-hitting branched covers of the smallest Titz--Witzel complex are sofic
distinct_from:
  titz-witzel-kernel-sofic: that is soficity of the lattice itself; this is soficity of the torsion-free hyperbolic CAT(0) groups of its branched covers satisfying (G) and (H), groups that are not simple and need not have property (T).
  nonsofic-hyperbolic-group: that asks for some nonsofic hyperbolic group; this asserts soficity for one explicit class of hyperbolic 2-complex groups, so its failure would answer that claim.
---

**OPEN.**  Let `X -> Y_1^2` be a finite branched cover satisfying the branch
girth condition (G) and the flat-hitting condition (H) of
`flat-hitting-branched-covers-have-hyperbolic-pi1`.  The claim is that
`pi_1(X)` is sofic.  Residual finiteness of `pi_1(X)` would suffice.

By `flat-hitting-branched-covers-have-hyperbolic-pi1`, `pi_1(X)` is a
torsion-free hyperbolic group acting freely and cocompactly on a CAT(0)
triangle complex whose vertex links are:
* the base links `GQ(2,2)` and `K_(3,3)` at unbranched vertices;
* connected covers of these of girth at least 10, respectively 6, at branch
  vertices.

The claim is implied by soficity of all hyperbolic groups, which is open.
No cubulation theorem is known to apply: `C~_2` triangle complexes carry no
evident wall structure.  So this is a genuine prerequisite, independent of
`titz-witzel-flat-hitting-sparse-branched-covers`: either can fail without
the other.

Two sub-routes would be natural.
* **Cubulation.**  Find a cocompact wallspace on `X~`, for instance from
  branch-vertex girth.  Then Agol's theorem
  (`hyperbolic-cubulated-groups-are-residually-finite`) finishes.
* **Hierarchy.**  Split `pi_1(X)` along quasiconvex subgroups carried by
  locally convex subcomplexes around branch vertices.
