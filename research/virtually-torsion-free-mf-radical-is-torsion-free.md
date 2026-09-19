---
rg: 2
id: virtually-torsion-free-mf-radical-is-torsion-free
kind: claim
title: The MF radical of a virtually torsion-free group is torsion-free, so no finite subgroup of such a group carries a no-CE augmentation corner
distinct_from:
  virtually-torsion-free-infinite-mf-radical-gives-seed: that proves a dichotomy for virtually torsion-free hosts and a corner corollary; this shows the radical always lies in the core of any torsion-free finite-index subgroup, so the first branch of that dichotomy is just "H is MF" and its corner corollary has no instances.
  nonhyperlinear-finite-augmentation-corner-kills-mf: that concludes K <= Rad_MF(G) from a no-CE corner; this shows that conclusion is impossible for nontrivial K whenever K survives in some finite quotient, so the theorem only ever fires on finite subgroups inside the finite residual.
  full-mf-radical-seed-has-no-torsion-free-quotient: that kills torsion-generated full radicals in torsion-free quotients; this is about finite-index subgroups, and says torsion in any MF radical lies in the finite residual.
artifacts:
  - research/virtually-torsion-free-mf-radical-is-torsion-free-proof.md
  - research/mf-radical-functoriality.md
  - research/mf-positive-controls.md
---

**ESTABLISHED, NO PROPERTY `(T)`.**

**Theorem.**  Let `H` be a countable group.

1. **Torsion lies in the finite residual.**  `Rad_MF(H)` lies in every normal
   subgroup of finite index.  In particular every element of finite order in
   `Rad_MF(H)` lies in the finite residual `Res(H)`, the intersection of all
   finite-index subgroups.
2. **Virtually torsion-free hosts.**  If `E <= H` is torsion-free of finite
   index, then `Rad_MF(H) <= Core_H(E)`.  So `Rad_MF(H)` is torsion-free and
   `Rad_MF(H) intersect W(H) = 1`, where `W(H)` is the finite radical.
3. **Finite-quotient corner kill.**  Let `K <= H` be a nontrivial finite
   subgroup that meets some finite-index normal subgroup `M` trivially.  Then
   there is *no* unital star homomorphism `B -> q_K C[H] q_K` from a unital
   star algebra `B` without a Connes-embeddable tracial state.  The regular
   representation of `H/M` gives every such `B` a matrix trace.

**Corollaries.**

- (a) `virtually-torsion-free-host-no-ce-augmentation-corner` is **refuted**.
  Its data force `K intersect Core_H(E) = 1` with `K != 1`, which is part 3.
  So the route `property-t-free-seed-via-virtual-torsion-corner` is dead.
- (b) The corner corollary of `virtually-torsion-free-infinite-mf-radical-gives-seed`
  is vacuous.  A finite `K` with `K <= Rad_MF(H)` is trivial by part 2, so
  it never has infinite normal closure.
- (c) The dichotomy of that lemma collapses.  Case 1, `Rad_MF(H) <= W(H)`,
  means `Rad_MF(H) = 1`, that is `H` is MF.  So
  `property-t-free-torsion-free-fp-non-mf-seed` is *equivalent* to the
  existence of a finitely generated, recursively presented, virtually
  torsion-free group that is not MF.  No torsion corner can certify such a
  group.
- (d) For the explicit-witness corner hole
  `nonhyperlinear-bloop-finite-augmentation-corner`, any successful finite
  subgroup `K` must lie in the finite residual of its host.  This follows
  from `nonhyperlinear-finite-augmentation-corner-kills-mf` together with
  part 1.  So residually finite, virtually torsion-free and finitely generated
  linear hosts are all excluded, and so is any `K` with a nontrivial image in
  some finite quotient.

**Where the trace-corner gate dies.**  The obstruction
`torsion-free-seeds-need-kernel-descent-or-trace-corner` (Consequence 3) says
the derivation must pass a torsion conclusion (C) followed by a finite-index
trace (I).  Part 1 shows every torsion conclusion lands in the finite
residual.  A virtually torsion-free host has a torsion-free finite residual.
So the gate is closed on exactly the hosts the trace step needs.  The class
version, which covers every derivation, is
`virtually-torsion-free-residual-kills-radical-calculus`.
