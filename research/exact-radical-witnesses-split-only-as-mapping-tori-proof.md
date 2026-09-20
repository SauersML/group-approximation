---
rg: 2
id: exact-radical-witnesses-split-only-as-mapping-tori-proof
kind: route
title: FA of the normal Kazhdan kernel makes its fixed tree G-invariant, so every minimal G-tree is the chi-line with all stabilizers K
target: exact-radical-witnesses-split-only-as-mapping-tori
requires: []
artifacts:
  - research/exact-radical-witnesses-split-only-as-mapping-tori.md
---

## Proof

The full argument is the `## Proof` section of `exact-radical-witnesses-split-only-as-mapping-tori`.
Its steps are as follows.

1. **Watatani.** A Kazhdan group is FA, so `Fix(K)` is a nonempty subtree for any action on a
   tree without inversions.
2. **Normality.** `g Fix(K) = Fix(g K g^-1) = Fix(K)`, so `Fix(K)` is `G`-invariant.
3. **Minimality.** Nearest-point projection of a `K`-fixed vertex onto a minimal invariant
   subtree `T_0` is `K`-fixed. So `Fix(K) ∩ T_0` is a nonempty invariant subtree, hence equal to
   `T_0`.
4. **The minimal tree.** `K` acts trivially on `T_0`, so `Z = G/K` acts minimally on it. It
   either fixes a point or translates a line.
5. **Stabilizers.** On a line, `G/K` acts freely, so every stabilizer is `K`.
6. **Reduced graphs of groups.**
   - Their Bass--Serre trees are minimal.
   - So the only reduced splitting is one loop with vertex and edge group `K`, which is the
     mapping torus.
   - Bieri--Strebel HNN extensions are one-loop graphs, so their base and associated subgroups
     are `K`.
7. **One end.** A splitting over a finite group would need a finite edge group equal to the
   infinite `K`. `G` is not virtually `Z`, since `K` is infinite of infinite index. By
   Stallings, `G` is one-ended.
