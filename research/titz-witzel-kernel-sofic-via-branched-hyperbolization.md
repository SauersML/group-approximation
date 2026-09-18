---
rg: 2
id: titz-witzel-kernel-sofic-via-branched-hyperbolization
kind: route
title: Hyperbolize the Titz--Witzel complex by sparse girth-branching and induce soficity from the covers' hyperbolic groups
target: titz-witzel-kernel-sofic
requires:
  - titz-witzel-flat-hitting-sparse-branched-covers
  - titz-witzel-flat-hitting-branched-cover-groups-are-sofic
  - flat-hitting-branched-covers-have-hyperbolic-pi1
  - sparse-branched-covers-with-sofic-pi1-give-sofic-lattice
  - sofic-kernel-amenable-quotient-permanence
---

**OPEN (two independent open prerequisites).**

1. `titz-witzel-flat-hitting-sparse-branched-covers` gives branched covers
   `X_k -> Y_1^2` with `beta(X_k) -> 0` satisfying (G) and (H).
2. By `flat-hitting-branched-covers-have-hyperbolic-pi1`, each `pi_1(X_k)`
   is hyperbolic.  By `titz-witzel-flat-hitting-branched-cover-groups-are-sofic`,
   it is sofic.
3. Part 1 of `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`
   makes `pi_1(Y_1^2)` sofic.  The simple kernel has index two in it, so it
   is sofic as a subgroup.  (Soficity passes to subgroups; finite-index
   permanence gives the other direction.)

**The two prerequisites fail independently.**
* The first is finite combinatorics about branch sets in one exotic
  building.
* The second is soficity of explicit hyperbolic CAT(0) triangle-complex
  groups.

Any failure has to land in one of three places:
* a precise obstruction to hitting all flats sparsely;
* a nonsofic hyperbolic group;
* a separate dead end for the second prerequisite.

**Contrapositive (see `nonsofic-hyperbolic-group-from-titz-witzel-flat-hitting-covers`).**
If the kernel is nonsofic, the first prerequisite alone produces a nonsofic
hyperbolic group.  So proving the combinatorial prerequisite makes the
kernel's soficity problem at least as hard as, and a special case of, the
open question whether all hyperbolic groups are sofic.

**Structural fit with known obstructions.**
* Sparse branching is necessary for soficity (part 2 of the reduction).
* `no_local_model` forces branching.
* `titz-witzel-sparse-defect-needs-dense-generator-surgery` forces dense
  generator monodromy.  Branched covers built from scratch, rather than by
  editing exact sheets, have it automatically.
