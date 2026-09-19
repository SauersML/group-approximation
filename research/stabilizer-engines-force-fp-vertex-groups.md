---
rg: 2
id: stabilizer-engines-force-fp-vertex-groups
kind: claim
title: A finitely presented group between the derived stabilizer engine D(F_B) and F_B that contains B forces the vertex group B to be finitely presented; so D(F_B) or F_B finitely presented implies B finitely presented
distinct_from:
  fp-stabilizer-engines-need-decidable-vertex-groups: that derives only a solvable word problem for B from a finitely presented D(F_B); this derives a finite presentation of B, which is strictly stronger for BH purposes because it makes the engine route circular.
  free-factor-isotropy-of-fp-full-subgroups-is-fp: that is the general retraction theorem for any free-factor isotropy of a piecewise-D group; this is its specialization to the stabilizer engine, with the hypotheses checked on the compactified Bass–Serre tree.
---

**ESTABLISHED** by `stabilizer-engine-hypotheses-check-proof` (lane proof,
swarm-0917-w12-w12-bh-last1, 2026-09-18; elementary given the general retraction
theorem; not reviewed).

## Notation

`k >= 2`, `B` is a countably infinite group, `A = Z/k`, `D = A * B`. `X` is the
Bass–Serre tree of `D` compactified by its `B`-vertices, and `F = F_B = [[D ⋉ X]]` is
the stabilizer engine, with commutator subgroup `D(F)`. This is the setting of
`free-product-boundary-groupoids-carry-the-vertex-group-homology`. Only its
definitions are used here, not its imported theorems. `v = 1B` is the base vertex, and
`B ≤ F` acts through `D`.

## Statement

1. If `E` is a finitely presented group with `D(F) ≤ E ≤ F` and `B ≤ E`, then `B` is
   finitely presented. More precisely, `B` is a retract of a finitely presented group.
2. If `F_B` is finitely presented, then `B` is finitely presented.
3. If `B` is finitely generated and `D(F_B)` is finitely presented, then `B` is finitely
   presented.
4. If `B` is perfect, then `B ≤ D(F_B)`, and every group `E` with `D(F_B) ≤ E ≤ F_B` is
   finitely presented only if `B` is.

## Consequence for Boone–Higman

A stabilizer engine can only present an input that is already finitely presented.
Combined with `fp-stabilizer-engines-need-decidable-vertex-groups`, a finitely
presented `D(F_B)` needs `B` to be finitely presented **and** to have solvable word
problem. So the route `boone-higman-via-stabilizer-engines` needs a finitely presented
simple envelope `S` of the input before it starts. That is Boone–Higman for the input.
The route is circular, and its hole
`simple-inputs-have-finitely-presented-stabilizer-engines` is false
(`regular-cyclic-twisted-core-has-non-fp-stabilizer-engine`).
