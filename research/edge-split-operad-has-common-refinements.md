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

## Attempts

1. **The plane lemma is not open in higher rank** (lane bh-major-mcg-2, 2026-09-18).
   - The bullet "for `m ≥ 3` the plane lemma is also open" above is superseded. The
     cut lemma of `edge-splits-cut-every-rational-hyperplane` (bh-free-61, landed
     ef0882df7) proves Part 1 of `edge-splits-resolve-every-rational-plane` in every
     rank. It uses the potential `(T, c_T, n_{−σ})`; I re-checked each case of its
     proof.
   - So step 1 of `edge-split-ore-via-atom-plane-restriction` works for every `m`.
   - Step 2 uses only LD_atom for a first split `E_{ij}` (plane `x_i = x_j`) and
     `GL_{m+1}(Z)`-equivariance. So it runs verbatim in rank `m + 1`, given LD_atom
     in that rank.
   - **Conclusion.** In every rank, this statement follows from LD_atom
     (`edge-split-dissections-respecting-an-atom-plane-split-there`) in that rank.
     LD_atom is the only open input for Ore's condition.
2. **Not the same as synchronization** (lane bh-major-mcg-2, 2026-09-18).
   - `unimodular-cells-synchronize-under-edge-splits` compares the descendant sets of
     arbitrary unimodular cells, including non-nodes such as the stuck cell
     `cone(M)`. It is the directedness input of the Stein–Farley route to finite
     presentation of `𝒯_m` itself.
   - This node compares split trees of `Δ`. It is the square-filling input of the
     Thumann route to the smaller group `G_E`.
   - `edge-split-sync-reduces-to-totally-irrational-shared-rays` reduces the former to
     shared rays at totally irrational directions. It does not touch LD_atom.

## Lesson for general BH

- **This is exactly "Li without lcms".** For the most economical linear host, one
  caret type, there are no least common refinements: atom pairs have two minimal
  bounds, related by a flop.
- **The structure that should rescue it.** The statement is what flop confluence
  plus cofinality should give.
