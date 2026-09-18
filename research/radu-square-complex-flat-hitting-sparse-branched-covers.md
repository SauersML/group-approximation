---
rg: 2
id: radu-square-complex-flat-hitting-sparse-branched-covers
kind: claim
title: Radu's square complex has flat-hitting branched covers of arbitrarily small branching mass
distinct_from:
  titz-witzel-flat-hitting-sparse-branched-covers: that is the triangle-complex statement for Y_1^2, which needs a separate soficity input; here the covers are square complexes, so Agol's theorem makes this statement sufficient for soficity of Radu's lattice on its own.
  radu-bmw-lattice-sofic: that is soficity of the lattice; this is a finite combinatorial existence statement that implies it.
  radu-nilpotent-by-arithmetic-quotients-are-sofic: that approximates the lattice by marked limits of amenable-by-arithmetic quotients; this approximates it by cubulated hyperbolic groups of branched covers, with no marked limit.
artifacts:
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

**OPEN.**  Let `S_R` be Radu's square complex:
* 4 vertices, links `K_(3,3)`;
* universal cover `T_3 x T_3`;
* `pi_1(S_R)` of index four in `Gamma_R`
  (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`).

The claim: for every `eta > 0` there is a finite branched cover `X -> S_R`
(`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`) satisfying
three conditions.

1. `beta(X) < eta`.
2. **(G)** Every branch vertex has a link, a connected bipartite cover of
   `K_(3,3)`, of girth at least 6.
3. **(H)** For some `R`, every flat `R x R` grid of `T_3 x T_3`, lifted to
   `X` from any vertex, contains a branch vertex.

**Why it matters.**  By `radu-bmw-lattice-sofic-from-flat-hitting-branched-covers`,
this single statement makes `Gamma_R` sofic.  The covers are nonpositively
curved VH square complexes with hyperbolic `pi_1`, hence residually finite
by Agol and Haglund--Wise.  Conversely, if `Gamma_R` is nonsofic, this
statement is false.  A nonsoficity proof must then show that sparse branch
sets can never hit all flat grids.

**What any construction must look like.**
* An unbranched cover (`beta = 0`) contains flat grids, so branching is
  mandatory.
* (H) makes `B` `R`-dense, so `beta >~ 1/R^2` and `R -> infinity`.
* A product hitting set `A x A'`, with `A` meeting every length-`R` geodesic
  of each tree factor, is the obvious candidate.  It needs horofunction-type
  levels in each factor.  Those are invariant under no finite-index subgroup
  of an irreducible lattice (heuristic: an out-degree-one orientation of
  `T_3` fixes an end).  So branch sets must not be pulled back from tree
  coordinates.
* Radu's attempts record that sparse defects do not break horizontal strips
  over expander-like slices.  (H) concerns grids, not strips: it does not
  require strips to break.

## Attempts

* **Vertical slabs: finite-cover-based witnesses are dead
  (swarm-0917-w5-titz-sofic, 2026-09-17).**  Proved in
  `flat-hitting-branched-covers-open-vertical-kernel`.  Take
  `g = (xz)^(4j) in pi_1(S_R)`.  It lies in the free vertical kernel
  `Lambda_v`, so it fixes `T_h` pointwise, and it lies in the finite residual.

  Let `W` be the set of vertices at which every short conjugate of `g`
  lifts to a closed B-free loop.
  * Closed B-free loops propagate along B-free horizontal strips.
  * A long non-backtracking internal horizontal path, times the periodic
    vertical axis, lifts to a B-free flat, which (H) forbids.  So the internal
    graph on `W` is a forest.
  * At least `|W|` exits are needed, and exits inject into branch data.

  This gives `|W| <= 3 (L+1) P_L beta(X) n_X` under (H) alone; (G) is not
  needed.  Every finite cover closes `g` at every point.  So any witness that
  agrees with a finite cover on at least half of the rooted `L`-balls has
  `beta >= c_R/2`, independently of `R`.

  *Invariant:* the closed-slab set `W`.  *Where each construction fails:*
  * congruence covers plus planted branching, however `R`-dense;
  * random covers plus sparse surgery;
  * horofunction-level branch sets on finite covers.

  All fail at the forest exit count.

  *What survives:* witnesses whose local structure opens short conjugates of
  the mark at all but `O(beta)` of the points.  Their rooted `L`-balls are
  not those of finite covers, so the local combinatorics must already
  separate the finite residual.  The node stays OPEN.
