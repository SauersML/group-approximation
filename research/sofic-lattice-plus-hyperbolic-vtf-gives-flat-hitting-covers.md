---
rg: 2
id: sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers
kind: claim
title: If pi_1 of a compact CAT(0) triangle complex is sofic and 2-dimensional CAT(0) hyperbolic groups are virtually torsion-free, then it has flat-hitting girth-raising branched covers of arbitrarily small branching mass
distinct_from:
  titz-witzel-flat-hitting-sparse-branched-covers: that is the unconditional existence statement for Y_1^2; this is a conditional theorem for every compact locally CAT(0) piecewise Euclidean 2-complex, with soficity of pi_1 and a virtual torsion-freeness hypothesis as inputs
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that goes from covers to soficity (part 1) and from soficity to sparse covers with no girth or flat-hitting control (part 2); this upgrades part 2 to covers with (G) and (H), paying with one virtual torsion-freeness hypothesis
  flat-hitting-branched-covers-have-hyperbolic-pi1: that shows covers with (G) and (H) have hyperbolic pi_1; this runs the other way, building such covers from an orbihedral hyperbolic group through a torsion-free finite-index subgroup
  two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free: that is the open hypothesis used here; this is the implication, proved unconditionally
---

**ESTABLISHED** (proof: `sofic-plus-vtf-flat-hitting-covers-proof`).
Unreviewed.

Let `Y` be a finite connected piecewise Euclidean 2-complex with finitely many
shapes, whose closed cells embed and whose vertex links each contain a cycle.
Assume `Y` is locally CAT(0), and write
`G = pi_1(Y)` and `Delta` for the universal cover. Branched covers, the degree
`d_x` and the branching mass `beta` are as in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`. Fix a combinatorial
girth `g_y` for each vertex `y` of `Y` such that `g_y` times the smallest edge
angle of `Lk(y)` exceeds `2 pi`.

**Theorem.** Assume both of the following.
* **(S)** `G` has a sofic subgroup of finite index.
* **(V2)** Every word-hyperbolic group acting properly and cocompactly by
  cellular isometries on a CAT(0) piecewise Euclidean 2-complex with finitely
  many shapes is virtually torsion-free.

Then for every `eta > 0` there are `R > 0` and a finite connected branched cover
`X' -> Y` with branch set `B'` satisfying three conditions.
1. `beta(X') < eta`.
2. **(G)** At every `b in B'` over `y`, `Lk(b)` has girth at least `g_y`.
3. **(H)** No locally isometric map from the closed Euclidean `R`-disk to
   `X' \ B'` exists. In particular, no flat `R`-disk of `Delta`, lifted to `X'`
   from any vertex, avoids `B'`.

**Specialisation.** Take `Y = Y_1^2`, with `g = 10` at `v, w` (edge angle
`pi/4`) and `g = 6` at the `u_i` (edge angle `pi/2`). Then the conclusion is
exactly `titz-witzel-flat-hitting-sparse-branched-covers`. Hypothesis (S) is
`titz-witzel-kernel-sofic`, because `K` has finite index in `pi_1(Y_1^2)`.

**Consequences for the graph.**
* With `titz-witzel-kernel-sofic-via-connected-link-covers`, under (V2) the
  flat-hitting target for `Y_1^2` is *equivalent* to soficity of the simple
  Kazhdan kernel `K`.
* Contrapositive: if `K` is sofic but `titz-witzel-flat-hitting-sparse-branched-covers`
  fails, then some 2-dimensional CAT(0) hyperbolic group is not virtually
  torsion-free. By `hyperbolic-rf-question-equals-vtf-question`, some hyperbolic
  group is then not residually finite. So a refutation of the flat-hitting
  target is worth either a nonsofic group or a non-residually-finite hyperbolic
  group.
* The combinatorial difficulty of flat-hitting (random hitting sets, girth) is
  entirely absorbed. What remains is one soficity question and one torsion
  question.
