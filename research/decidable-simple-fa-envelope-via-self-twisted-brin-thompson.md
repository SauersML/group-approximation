---
rg: 2
id: decidable-simple-fa-envelope-via-self-twisted-brin-thompson
kind: route
title: The self-twisted Brin-Thompson group of a decidable group is a decidable simple FA envelope
target: decidable-groups-embed-in-decidable-simple-fa-groups
requires: [twisted-brin-thompson-fa-from-simplicity-by-tree-geometry, self-twisted-bt-group-fp-embedding-iff-solvable-wp]
---

Let `G` be a finitely generated group with solvable word problem, and let
`Γ = G·V_G` be the twisted Brin–Thompson group of the translation action of `G`
on itself.

1. **Envelope.** By Belk–Bleak–Matucci–Zaremsky, *Progress around the Boone–Higman
   Conjecture*, arXiv:2306.16356, Theorem 4.13, as quoted in
   `self-twisted-bt-group-fp-embedding-iff-solvable-wp-citation`: "If G is a
   finitely generated group then G·V_G is a finitely generated simple group, and G
   embeds isometrically into G·V_G."
2. **Word problem.** By `self-twisted-bt-group-fp-embedding-iff-solvable-wp`
   ((4)⇒(3)), `Γ` has solvable word problem.
3. **FA.** The translation action is faithful and has one orbit, and `G` is finitely
   generated. So by `twisted-brin-thompson-fa-from-simplicity-by-tree-geometry`, `Γ` has
   property FA.

So `G <= Γ`, and `Γ` is a finitely generated simple group with FA and solvable word problem. `∎`

**What this route adds beyond a Kazhdan host.** The envelope is the canonical host of the
permutational Boone–Higman programme (`type-a-action-gives-boone-higman-for-subgroups`).
Its FA is proved from the brick calculus and two imported theorems of Belk–Zaremsky, with no rigidity input.
Here `G` itself need not have FA. And no finitely generated twisted Brin–Thompson group splits
as a nontrivial amalgam or HNN extension.
