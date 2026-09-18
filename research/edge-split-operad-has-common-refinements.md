---
rg: 2
id: edge-split-operad-has-common-refinements
kind: claim
title: Any two edge-split dissections of a unimodular simplex cone have a common edge-split refinement
distinct_from:
  edge-split-operad-satisfies-ore: that bundles Ore's condition with finite type of the spine; this is Ore's condition alone, the half that the plane lemma and the atom-plane rearrangement address.
  edge-splits-resolve-every-rational-plane: that gives a common geometric refinement; this asks for a common refinement in the operad order, where each dissection is refined by further edge splits of its own pieces.
---

**OPEN** (lane bh-free-54, 2026-09-18).
- For `m = 2` it reduces, by `edge-split-ore-via-atom-plane-restriction`, to
  `edge-split-dissections-respecting-an-atom-plane-split-there`. That statement is
  checked exhaustively to 7 pieces, and its proof is complete except for one
  sub-case.
- For `m ≥ 3` the plane lemma is also open (greedy evidence only).

## Statement

Fix `m ≥ 2`. For any two edge-split dissections `D_1, D_2` of `Δ = cone(e_0, …, e_m)`,
there is an edge-split dissection `D` with `D ≥_E D_1` and `D ≥_E D_2`. That is, `D`
is obtained from each of them by further edge-midpoint splits of pieces. Notation is
as in `edge-split-operad-satisfies-ore`.

## Why it matters

- Cancellation holds automatically, so this is the cancellative calculus of
  fractions for `𝒪_E` in Thumann's theorem.
- With it, `ore-operad-groups-contain-the-derived-full-group` puts `D(𝒯_m)`, and so
  every perfect subgroup of `𝒯_m`, inside the edge-split group `G_E`.
- The remaining input for Boone–Higman of closed mapping class groups is finite type
  (the spine half of `edge-split-operad-satisfies-ore`), via
  `closed-mcg-bh-via-edge-split-operad`.

## Lesson for general BH

- **This is exactly "Li without lcms".** For the most economical linear host, one
  caret type, there are no least common refinements: atom pairs have two minimal
  bounds, related by a flop.
- **The structure that should rescue it.** The statement is what flop confluence
  plus cofinality should give.
