---
rg: 2
id: edge-split-dissections-respecting-an-atom-plane-split-there
kind: claim
title: An edge-split dissection of the standard triangle cone that no piece of which crosses a first-split plane is an edge-split refinement of that first split
refuted_by:
  - edge-split-order-is-not-geometric-refinement
distinct_from:
  edge-splits-resolve-every-rational-plane: that shows edge-split dissections can be made to respect any rational plane; this says that once one respects a first-split plane, it can be rearranged to split there first, which is the operad-order statement.
  edge-split-operad-satisfies-ore: that is Ore's condition plus finite type; this local rearrangement statement is the one input that, with the plane lemma, would give Ore's condition.
---

**REFUTED** (lane bh-free-54, 2026-09-18, second pass) by
`edge-split-order-is-not-geometric-refinement`.
- **The counterexample.** A 17-piece split tree respects `x_0 = x_1`, yet one of its
  pieces, bh-free-61's depth-five cell `cone((3,0,1), (2,1,1), (2,2,1))`, lies in
  `{x_0 ≥ x_1}` without descending from that child. The statement fails for every
  `m ≥ 2`.
- **Where it falls.** The counterexample's first split is at `(0, 2)`, and its half
  `K` splits first at the far edge. So it lies in the open sub-case below, and the
  proved sub-cases are not contradicted.
- **Consequences.** Consequences 1–3 below are false as stated. The exhaustive checks
  to 7 pieces are correct but too small to see the counterexample. The replacement
  reduction of Ore's condition is
  `edge-split-ore-iff-synchronization-and-tree-domination`.
- The original text follows as a record.

Originally: **OPEN** (lane bh-free-54, 2026-09-18), with a partial proof and
exhaustive checks up to 7 pieces. Stated for `m = 2`.

## Statement (LD_atom)

- Let `D ∈ 𝒪_E(Δ)`, with `Δ = cone(e_0, e_1, e_2)`, and suppose no piece of `D` has
  interior meeting the plane `x_i = x_j`.
- Then `D ≥_E E_{ij}`: the restriction of `D` to each half `{x_i ≥ x_j}` and
  `{x_j ≥ x_i}` is an edge-split dissection of that half, in the half's own frame.
- By `GL_3(Z)`-equivariance of edge splits, the same statement then holds for every
  unimodular cone and each of its three first splits.

## Consequences

1. **Geometric refinement implies operad refinement.** If `D, D' ∈ 𝒪_E(P)` and `D`
   refines `D'` geometrically, then `D ≥_E D'`.
   - Induct on `|D'|`. Write `D' = E_a ∘ (X, Y)`. Then `D` respects `E_a`'s plane,
     so LD_atom splits it at `a`.
   - Each half-restriction of `D` refines `X` or `Y` geometrically. Apply the
     induction hypothesis in the half's frame.
2. **Ore's condition for `𝒪_E` at `m = 2`.** Given `D_1, D_2`,
   `edge-splits-resolve-every-rational-plane` gives some `D ∈ 𝒪_E(Δ)` refining both
   geometrically. By Consequence 1, `D ≥_E D_1, D_2`. This is the route
   `edge-split-ore-via-atom-plane-restriction`.
3. **The spine becomes purely geometric.** `≥_E` coincides with geometric refinement
   on `𝒪_E`-dissections.

## Partial proof

Induct on `|D|`, writing `D = E_a ∘ (D_1, D_2)` with `a ≠ (01)` and target plane
`Π = {x_0 = x_1}`. Swapping `0 ↔ 1` fixes `Π`, so take `a = (02)`, with halves
`K = cone(e_0, e_1, v_{02})` and `K' = cone(v_{02}, e_1, e_2)`.

- **In `K'`.** The plane `Π` is the first-split plane at the edge `(v_{02}, e_1)`,
  with midpoint `c`. By induction, `D_2` splits there, into `cone(v_{02}, c, e_2)`
  and `cone(c, e_1, e_2)`.
- **In `K`.** The plane `Π` is the *medial line* from `v_{01} = e_0 + e_1` to
  `c = e_1 + v_{02}`. It cuts off the corner `C = cone(v_{01}, e_1, c)` and leaves the
  quadrilateral `Q = (e_0, v_{01}, c, v_{02})`.
- **The two halves of `E_{01}`.**
  - `H_2 = C ∪ cone(c, e_1, e_2)` is `H_2`'s own first split at `c`.
  - `H_1 = Q ∪ cone(v_{02}, c, e_2)` is split hierarchically in exactly two ways.
    They are the flop pair of `edge-split-operad-satisfies-ore` (diagonal `e_0 — c`,
    or `v_{01} — v_{02}`).
- **Reduction.** LD_atom in this case follows once `D_1` refines the medial line
  through one of its two minimal resolutions. Those resolutions are `R_1`, the split
  at `(e_0, e_1)` then at `(e_1, v_{02})`, and `R_2`, the same in the other order.
- **Proved sub-cases.** If the first split of `D_1` is at `(e_0, e_1)` or at
  `(e_1, v_{02})`, the medial line becomes a first-split line of a half. Induction
  gives `D_1 ≥_E R_1` or `R_2`. `D` is then rewritten explicitly into
  `E_{01} ∘ (…)`; this is the flop relation.
- **Open sub-case.** The first split of `D_1` is at the far edge `(e_0, v_{02})`.
  - In the two halves the medial line becomes a *unit-corner* line with values
    `(1, −1, 2)` or `(2, −1, 1)` on the frame.
  - So the induction closes on the family of unit-corner lines `(α, −1, γ)`. These
    cut off the node `cone(a_1, a_0 + αa_1, γa_1 + a_2)` at a vertex of value `−1`.
  - What is missing is the corresponding statement for that family: a dissection
    respecting such a line is `≥_E` one of its finitely many minimal resolutions.

## Evidence (MSI, exhaustive)

- **LD_atom.** 106830 instances, every (edge-split dissection with at most 7 pieces,
  respected first-split plane) pair. **0 violations.**
- **The stronger LD_gen.** Whenever a node (an element of the edge-split monoid
  `M_E`) is a union of at least 2 but not all pieces of `D ∈ 𝒪_E(Δ)`, the
  restriction is edge-split in the node's frame. 45075 instances, dissections with
  at most 6 pieces. **0 violations.**
- Scripts `ldatom.py` and `ldgen.py`, with outputs, are in
  `research/artifacts/gq-bh-free-54-edge-split-ore-tests.md`.

## Lesson for general BH

- **The non-LCM gate is local.** For a dissection operad, the gate reduces to a
  one-step rearrangement property: a dissection that respects a generator's cut can
  be rearranged to make that cut first.
- **How the rearrangement works.** It uses the flop relation, the operad's only
  non-trivial relation seen so far.
- **Garside analogue.** This is the analogue of Garside's "divisibility is decided
  by the geometry". Once it holds, Ore's condition is automatic from cofinality, and
  the spine is computed geometrically.
