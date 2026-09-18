---
rg: 2
id: twisted-brin-thompson-fa-from-simplicity-by-tree-geometry
kind: claim
title: Belk-Zaremsky simplicity and finite generation alone force property FA for twisted Brin-Thompson groups, by elementary tree geometry
distinct_from:
  fg-perfect-wreath-c2-has-property-fa: that gives the non-simple FA envelope A wr C_2; this gives FA for the simple groups SV_G themselves.
  displaced-perfect-subgroups-are-elliptic-in-tree-actions: that is the abstract tree criterion; this verifies its hypotheses in SV_G through the brick calculus and simplicity.
  brin-thompson-groups-nv-lack-property-t: that concerns property (T), which is much stronger than FA; SV_G contains V, which is a-T-menable, and FA holds anyway.
---

Let `G` act faithfully on a nonempty set `S` with finitely many orbits, with `G`
finitely generated. Then the twisted Brin–Thompson group `SV_G` of Belk–Zaremsky
has Serre's property FA: every action on a tree has a global fixed point.

In particular, for every finitely generated group `G`, the self-twisted group
`G·V_G` (translation action) is a finitely generated simple group with FA containing `G`.

The content is in how the result is certified. The only inputs are the definitions and
Theorems A and 3.4 of Belk–Zaremsky, together with geodesics in trees. There is
no hyperbolic-space, quasimorphism or cube-complex input. In parallel, worker
swarm-0917-w4-bh-fa-envelopes is landing the id twisted-brin-thompson-groups-have-property-fa,
which imports property NL from Fournier-Facio–Wu–Zaremsky (arXiv:2603.24687). The present
claim is an independent certificate of its part (FA), and the proof route below can
be retargeted there as a second route.

The proof is in `twisted-brin-thompson-fa-from-simplicity-by-tree-geometry-proof`.
1. Rigid stabilizers of proper clopen sets are copies of `SV_G`, so they are simple
   and perfect.
2. Each such stabilizer can be displaced off its support, so it commutes with a
   conjugate of itself. By `displaced-perfect-subgroups-are-elliptic-in-tree-actions`,
   it fixes a vertex.
3. A partition of the cube into four bricks gives three stabilizers whose pairwise
   unions are proper. A join lemma, which follows from simplicity, shows that they
   generate `SV_G`. Helly glues their fixed sets.

**Calibration.** Thompson's `F` does not have FA, since it maps onto `Z^2`. Its rigid stabilizers are
copies of `F` and are not perfect, so step 2 fails exactly at perfectness. For
`V`, which is `SV_G` with `|S| = 1` and `G` trivial, the result recovers the known fact
that `V` has FA; see the survey remark in
`decidable-groups-embed-in-decidable-simple-fa-groups`. The groups `nV` are the case with `|S| = n` and trivial `G`.
