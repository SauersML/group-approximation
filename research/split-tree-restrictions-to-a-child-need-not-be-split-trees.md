---
rg: 2
id: split-tree-restrictions-to-a-child-need-not-be-split-trees
kind: claim
title: A ten-piece split tree of the triangle cone respects a first-split plane, and its restriction to one child is a dissection into that child's own descendants that is not a split tree
artifacts:
  - research/artifacts/gq-bh-major-mcg-2-ldatom-counterexample.md
distinct_from:
  edge-split-order-is-not-geometric-refinement: that refutes LD_atom with a 17-piece split tree containing a cell that descends from the simplex but not from the child it lies in, a synchronization failure; here every piece in the child descends from the child, so the failure is purely one of tree structure, and it has 10 pieces.
  edge-split-descendant-dissections-are-tree-dominated: that is tree domination (TD, OPEN); this is an instance of the hypothesis of TD arising as the restriction of a split tree, and it needs refinement (two extra splits suffice), so TD cannot hold without refinement even for such restrictions.
  edge-split-dissections-respecting-an-atom-plane-split-there: that is the refuted LD_atom; this refutes it a second, independent way, inside its own open far-edge sub-case.
---

**ESTABLISHED** (lane bh-major-mcg-2, 2026-09-18). It is an explicit finite example,
checked by hand and by exact integer arithmetic (script and output in the artifact;
one MSI process, under a second). The descendance test is calibrated on the stuck
cell and on the depth-five cell of `edge-split-descendants-are-not-factor-closed`.
No priority claimed.

## Statement

Notation of `edge-split-ore-iff-synchronization-and-tree-domination`, with `m = 2`,
`Δ = cone(e_0, e_1, e_2)`, `H_1 = cone(e_0, v_{01}, e_2) = {x_1 ≤ x_0}` and
`H_2 = cone(v_{01}, e_1, e_2)`.

There is `D ∈ Trees(Δ)` with 10 pieces such that:
1. every piece of `D` lies in `H_1` or in `H_2`;
2. **every piece of `D|_{H_1}` lies in `Desc(H_1)`**;
3. `D|_{H_1} ∉ Trees(H_1)`, so `D ≱_E E_{01}`;
4. two further edge splits give `D^* ≥_E D` with `D^* ≥_E E_{01}` (12 pieces).

## The dissection

Put `v_{02} = (1,0,1)`, `u = (2,0,1)`, `w = (2,1,1)`, `z = (2,2,1)`, `c = (1,1,1)`.
Build the split tree as follows, splitting at the given edge each time.
1. `Δ` at `(e_0, e_2)`: this gives `K = cone(e_0, e_1, v_{02})` and
   `K' = cone(v_{02}, e_1, e_2)`.
2. `K'` at `(v_{02}, e_1)`: this gives `P_7 = cone(v_{02}, c, e_2)` and
   `P_8 = cone(c, e_1, e_2)`.
3. `K` at its far edge `(e_0, v_{02})`: this gives `K_a = cone(e_0, e_1, u)` and
   `K_b = cone(u, e_1, v_{02})`.
4. `K_a` in three steps:
   - at `(e_1, u)`, leaving `P_1 = cone(e_0, w, u)`;
   - then at `(e_1, w)`, leaving `P_2 = cone(e_0, z, w)`;
   - then at `(e_0, e_1)`, giving `N_A = cone(v_{01}, e_1, z)` and
     `P_3 = cone(e_0, v_{01}, z)`.
5. `K_b` in three steps:
   - at `(u, e_1)`, leaving `P_4 = cone(u, w, v_{02})`;
   - then at `(w, e_1)`, leaving `P_5 = cone(w, z, v_{02})`;
   - then at `(e_1, v_{02})`, giving `N_B = cone(z, e_1, c)` and
     `P_6 = cone(z, c, v_{02})`.

## Proof

1. **The plane is respected.** `x_0 − x_1` takes these values on the rays:
   `e_0: 1`, `e_1: −1`, `e_2: 0`, `v_{01}: 0`, `v_{02}: 1`, `u: 2`, `w: 1`, `z: 0`,
   `c: 0`. It is `≥ 0` on `P_1, …, P_7` and `≤ 0` on `N_A`, `N_B`, `P_8`.
2. **Each piece descends from `H_1`.** In the frame of `H_1` the coordinates are
   `(x_0 − x_1, x_1, x_2)`. For each `P_i`, `i ≤ 7`, the row-reduction test of
   `edge-split-descendants-are-not-factor-closed` reaches a permutation matrix. For
   example:
   - `P_2` has rows `(1,0,1), (0,2,1), (0,1,1)`. Subtract row 2 from row 1, then row 1
     from row 2, then row 2 from row 0.
   - `P_5` has rows `(1,0,1), (1,2,0), (1,1,1)`. Subtract row 0 from row 2, then row 2
     from row 1 twice, then row 1 from row 0.
3. **The restriction is not a split tree.** A split tree of `H_1` other than `H_1`
   itself respects one of the three first splits of `H_1`, and each of them is
   straddled:
   - `v_{02}` (plane `x_0 − x_1 − x_2 = 0`) is straddled by `P_2`, with values
     `1, −1, 0`;
   - `c` (plane `x_1 = x_2`) is straddled by `P_5`, with values `0, 1, −1`;
   - `(2,1,0)` (plane `x_0 = 2x_1`) is straddled by `P_2`, with values `1, −2, 0`.
4. **Domination.** Split `P_2` and `P_3` at their edges `(e_0, z)` (at `(3,2,1)`).
   Then `D^*|_{H_1}` is a split tree, with split points in this order:
   - `H_1` at `v_{02}`;
   - `cone(e_0, v_{01}, v_{02})` at `w`, then its children at `u` and at `(3,2,1)`;
   - `cone(v_{02}, v_{01}, e_2)` at `c`;
   - `cone(v_{02}, v_{01}, c)` at `z`;
   - `cone(v_{02}, v_{01}, z)` at `w`;
   - `cone(w, v_{01}, z)` at `(3,2,1)`.

   `D|_{H_2}` is already a split tree: split at `c`, then at `z`.

## Where it comes from

This is the far-edge sub-case of LD_atom, left open in
`edge-split-dissections-respecting-an-atom-plane-split-there`, in its smallest form.
- The medial line of `K` becomes the unit-corner lines `(1, −1, 2)` in `K_a` and
  `(2, −1, 1)` in `K_b`.
- On the negative side nothing goes wrong. The negative side of a unit-corner line
  `(α, −1, γ)` is a unimodular descendant `N`, and the far-edge split restricts to an
  edge split of `N`: here `N_A ∪ N_B` is split at `z`.
- The minimal resolutions of `(α, −1, γ)` are indexed by interleavings of `α` splits
  at `(a_0, a_1)` with `γ` splits at `(a_1, a_2)`. The words `tts` in `K_a` and `sst`
  in `K_b` leave positive pieces that fit no first split of `H_1`.

## Lesson for general BH

- **Two independent obstructions.** Rearranging a dissection so that a respected cut
  comes first fails in non-LCM dissection operads for two independent reasons:
  - synchronization: a piece may not descend from the half it lies in
    (`edge-split-order-is-not-geometric-refinement`);
  - tree structure, even when every piece descends: pieces made by different
    resolution orders of the same line do not assemble into one tree.
- **Consequence.** Both halves of the Ore reduction (Sync′ and TD) are genuinely
  needed. TD genuinely needs refinement, already for restrictions of split trees to
  a child.
- **Cost of the repair.** It was cheap here: two splits in the pieces that straddle.
  So a TD proof should look for a bounded repair near the straddling pieces, not for
  a global rearrangement.
