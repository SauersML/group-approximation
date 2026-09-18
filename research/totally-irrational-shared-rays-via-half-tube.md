---
rg: 2
id: totally-irrational-shared-rays-via-half-tube
kind: route
title: Shared rays at every totally irrational direction, in every rank, from the half-tube lemma and Dirichlet's theorem
target: edge-split-cells-share-rays-at-totally-irrational-directions
requires:
  - half-tube-lattice-points-are-edge-split-vertices
---

Lane bh-major-mcg-2, 2026-09-18. Lane proof; one referee PASS (bh-ref-engines, 2026-09-18).

1. **Rank two.** `(TI_1)` holds by the Stern–Brocot argument in the target node.
2. **Rank at least three.** For `m ≥ 2`, a totally irrational `ξ` is generic in the sense
   of `half-tube-lattice-points-are-edge-split-vertices`: it lies on no rational
   hyperplane.
   - The corollary of that node gives a primitive `w` that is a vertex of a cell of
     `Desc(c)` containing `ξ` and of a cell of `Desc(F)` containing `ξ`. Those two cells
     share the ray `w`, which is `(TI_m)`.
   - Checked here: the coordinates `B_s^{-1}w` are automatically nonnegative. Each
     is within `1/2` of a positive multiple of a positive vector, so it exceeds `−1/2`.
     The lemma's proof never uses strict positivity of `u`.
3. **Consequence.** With `edge-split-sync-reduces-to-totally-irrational-shared-rays`,
   the route `edge-split-sync-via-totally-irrational-shared-rays` gives a second proof
   of `(Sync_m)` in every rank. It is independent of bh-free-61's own route
   `unimodular-cells-synchronize-under-edge-splits-proof`, except for the shared
   half-tube lemma. The rational strata are handled differently: face cut, link lift
   and face lemma here.

## Lesson for general BH

- **The tube, not the path, decides.** For free-choice subdivision hosts, a reachability
  tube around a direction settles the Serret-type gate at once. In
  `edge-split-cells-share-rays-at-totally-irrational-directions`, the gate had looked
  like a Diophantine problem needing flow recurrence and a tracking argument.
- **The mechanism is local and rank-free.** It is a sign pigeonhole on rounding errors,
  which needs rank at least three.
- **Check it first.** For any higher-rank lattice host, ask whether the free choice
  makes the set of reachable lattice points contain a tube of fixed width. If it does,
  shared vertices come from Dirichlet, and no dynamics is needed.

## Referee (bh-ref-engines, 2026-09-18): PASS

- **Rank at least three.** "Totally irrational" (on no rational hyperplane) is exactly "generic" in the
  half-tube node. The half-tube corollary (referee PASS, bh-ref-kourovka-b) gives a primitive `w` that is a
  vertex of cells of `Desc(c)` and `Desc(F)` both containing `ξ`. So they share the ray `w`, which is
  `(TI_m)`.
- **Nonnegativity.** The remark matches the half-tube referee's note.
- **Rank two.** `(TI_1)` is the Stern–Brocot case.
- **Consequence.** I checked the reduction `edge-split-sync-reduces-to-totally-irrational-shared-rays` in
  full; see its Referee section. So `(Sync_m)` holds in every rank by this second route. The only imported
  input is the cut lemma `edge-splits-cut-every-rational-hyperplane`.
