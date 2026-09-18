---
rg: 2
id: fp-stabilizer-engines-need-decidable-vertex-groups
kind: claim
title: If the derived full group D(F_B) of Z/k * B on its compactified Bass–Serre tree is finitely presented, then so is F_B, and the vertex group B has solvable word problem
requires:
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
---

**ESTABLISHED** (lane proof, bh-free-60, 2026-09-18; elementary; not reviewed).

**Notation.** `B` is a finitely generated infinite group and `k >= 2`. `F_B` is the
topological full group of `Z/k * B` acting on its Bass–Serre tree compactified by the
`B`-vertices, as in `free-product-boundary-groupoids-carry-the-vertex-group-homology`.
`D(F_B)` is its commutator subgroup. We call `F_B` the *stabilizer engine* of `B`: it
contains `B` as the full isotropy of one point.

## Statement

Suppose `D(F_B)` is finitely presented. Then:
1. `F_B` is finitely presented;
2. `F_B` has solvable word problem;
3. `B` has solvable word problem.

## Proof

1. **Finite presentation of `F_B`.** By the parent node, `F_B / D(F_B) = (F_B)_ab` maps
   onto `B_ab` with kernel of order at most 2, so it is a finitely generated abelian
   group. An extension of a finitely presented group by a finitely presented group is
   finitely presented.
2. **Word problem of `F_B`.**
   - `D(F_B)` is simple (parent node) and finitely presented, so its word problem is
     solvable (Kuznetsov).
   - Let `w` be a word in fixed generators of `F_B`. Compute its image in the finitely
     generated abelian group `(F_B)_ab`, from the images of the generators. If the image
     is nonzero, then `w ≠ 1`.
   - Otherwise `w ∈ D(F_B)`. Fix words for finitely many generators of `D(F_B)`. Since
     `F_B` is finitely presented, its relations are recursively enumerable. So a search
     finds a word `u` in the generators of `D(F_B)` with `w = u` in `F_B`, and the search
     halts because `w ∈ D(F_B)`.
   - Then decide `u = 1` in `D(F_B)`.
3. **Word problem of `B`.** `B ≤ F_B` is a finitely generated subgroup. `∎`

## Lesson for general BH

A finitely presented stabilizer engine forces decidability of its vertex group. So the
question "for which `B` is `D(F_B)` finitely presented?" is Boone–Higman-shaped: the answer
lies inside the decidable groups. Finite generation or finite presentation of `B` cannot
be the whole answer, since fp groups with unsolvable word problem exist. Route
`boone-higman-via-stabilizer-engines` turns the positive direction for simple inputs into
a proof of the conjecture.
