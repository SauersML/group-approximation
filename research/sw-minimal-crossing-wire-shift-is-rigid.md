---
rg: 2
id: sw-minimal-crossing-wire-shift-is-rigid
kind: claim
title: SW-deterministic self-simulation forces causal rules (a top bit sees only bottom bits to its left); with a diagonal-time rule this is met, and the minimal crossing-wire shift laid out this way is free, minimal, quantum rigid and anti-diagonally deterministic
artifacts:
  - research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md
  - research/artifacts/gq-bh-g2-fixedpoint-a-diagonal-time-layout.md
distinct_from:
  minimal-crossing-wire-fixed-point-shift-is-quantum-rigid: that uses a two-way head zone with inputs on all four sides; this computes the top and right colours from the left and bottom ones, so the shift is SW-deterministic.
  sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices: that states an SW Layout Lemma with a generic one-way CA zone; the causality lemma here shows that such a zone cannot write top bits to the left of bottom bits it reads, and gives a rule shape that avoids this.
---

Inputs this claim recorded under the older schema (not a proof; they do not establish it): `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid`, `sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices`.

**Part 1 ESTABLISHED; parts 2–3 CONDITIONAL on the diagonal-time layout**, written out at tile level in
`research/artifacts/gq-bh-g2-fixedpoint-a-diagonal-time-layout.md` (designed here, not verified line by
line). Lane bh-g2-fixedpoint-a, 2026-09-18, not reviewed; no priority claimed.

## 1. Causality lemma (established)

Let `τ` be SW-deterministic: each tile is fixed by its left and bottom colours. Tile an `N × N` block with
given bottom boundary colours `b_0, …, b_(N−1)` and left boundary colours `l_0, …, l_(N−1)`. By induction on
`x + y`, the tile at `(x, y)` depends only on `b_0, …, b_x` and `l_0, …, l_y`.

**Consequence.** If `τ` self-simulates, the simulated rule `Φ = (Φ_top, Φ_right)` must be *causal* for the
side encodings:
- entry `p` of `Φ_top(l, b)` depends only on `l` and `b_(≤p)`;
- entry `q` of `Φ_right(l, b)` depends only on `b` and `l_(≤q)`.

The top side of one macrotile is the bottom side of the next, so input and output bits share positions.
Hence a zone that reads all bottom bits cannot write top bits at their positions. The referee found the same
constraint independently (e1de4c7e75). **This affects any SW
fixed-point layout with a generic one-way CA zone**, including the Layout Lemma of
`sw-crossing-wire-tiles-give-free-rigid-sfts-on-kazhdan-lattices`.

## 2. Diagonal-time rule (the design)

Choose `τ`'s rule to be causal. Every tile type has one of these forms:
- `top = F(left)`, `right = G(bottom)`;
- a same-position copy: `top_p = bottom_p` (V), or `right_q = left_q` (H), with CROSS combining both.

In particular:
- **Coordinates.** The top coordinate `(i, j+1)` is read from the left edge, which carries `(i, j)`. The right
  coordinate `(i+1, j)` is read from the bottom edge.
- **Wire tiles.** FAN (bottom → top, right) and the two TURNs (left → up, bottom → right) already have these
  forms.
- **Zone cells.** A cell `i` at time `t` has:
  - bottom `x_t(i)`;
  - left `(x_t(i−1), x_t(i−2), x_t(i−3))`;
  - right `(x_t(i), x_t(i−1), x_t(i−2))`;
  - top `x_(t+1)(i) = F_U(x_t(i−3), x_t(i−2), x_t(i−1))`.

  With tape cell `c` at time `t` in column `c + 2t`, `F_U` is the local update of the universal machine
  `U`. The written-out tile family is §7 of the diagonal-time layout artifact.

**Macrotile layout.** One macrotile implements `Φ` with the following parts.
- **zone_T.** It sits upper left, at columns left of every top bit position and above every left bit position.
  It is fed by the left side and computes the role and `F(left)`.
- **zone_R.** It sits lower right, to the right of every bottom bit position and below every right bit
  position. It is fed by the bottom side and computes `G(bottom)`.
- **Combiners.** At each top bit position `p`, a tile selects either zone_T's value or `b_p` straight up. At
  each right bit position `q`, a tile selects either zone_R's value or the forwarded left bit. The select
  signal comes from the role.
- **Encoding.** The second vertical component sits above the first (`Q_2 > Q_1`), so `x(i−1)` moves from
  heights `Q_1` on the left to `Q_2` on the right, going right and up.
- **Crossings.**
  - Each left input fans out a horizontal copy that runs across all bottom-input columns.
  - Each bottom input fans out a vertical copy that runs across all left-input rows.
  - Box copies cross same-side pairs.
  - Every copy ENDs before the opposite margin, and before any output wire on its row.

All flows are up or right, and every rule is coordinate-fixed and `poly(log N_k)`-checkable (artifact §4). DR's
(p1)–(p4) and slots (SW islands) are added as in the minimal node.

## 3. Consequences (conditional on §2)

Let `Ω_SW` be the ground shift. Then:
1. **Free and minimal**, as in parts B–C of `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid-proof`.
   SW tiles are 2×2-determinate, so zone, crossing and fan-out windows get slots.
2. **1-rigid over every field**, by part A with A4:
   - the bottom and left inputs are pairwise crossed;
   - every other edge is reached by the face rule "right and top from left and bottom";
   - slot edges are scalars on phase summands.
3. **Anti-diagonal determinism.** The tile at `(i, j)` has its bottom edge on `(i, j−1)` and its left edge on
   `(i−1, j)`. So the anti-diagonal `x + y = c` determines `x + y = c + 1`.

## Lesson for general BH

- **Determinism has a price in self-simulation: causality.** Information in SW tilings flows up and to the
  right, and sides are shared. So the simulated rule must never need a bottom bit to its right.
- **Diagonal time pays it.** Outputs depend fully on the left, or fully on the bottom, never on both, so a
  universal CA still fits.
- Co-location and slots are untouched, so rigidity and minimality survive, and the shift gains a one-sided
  expansive direction.
