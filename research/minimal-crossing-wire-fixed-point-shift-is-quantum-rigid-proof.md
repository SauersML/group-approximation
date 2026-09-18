---
rg: 2
id: minimal-crossing-wire-fixed-point-shift-is-quantum-rigid-proof
kind: route
title: Run the crossing-wire rigidity proof level by level on the Durand–Romashchenko variable-zoom tile sets, show diversification slots are frame-forced hence classical, and reuse DR's minimality case analysis with slots for crossing windows
target: minimal-crossing-wire-fixed-point-shift-is-quantum-rigid
requires:
  - crossing-wire-fixed-point-tile-sets-are-quantum-rigid
  - fixed-point-wang-tile-rigidity-is-edge-family-commutation
---

Lane proof (bh-g2-fixedpoint-a, 2026-09-18). Not independently reviewed.

Notation is from the target and from `crossing-wire-fixed-point-tile-sets-are-quantum-rigid-proof`, cited as
Steps 1–5. "FLEF" means face-local edge family. DR is arXiv:1802.01461, TeX source md5 `8e17f728…`.

## A. Rigidity

By item 1 of `fixed-point-wang-tile-rigidity-is-edge-family-commutation`, it suffices to show that every FLEF
`P` of `τ_0` commutes.

**A1. Variable zoom.** Steps 1–5 never use that the tile set at level `k` is the same as at level 0. They use
only the following, at each level:
- (L0) coordinates and fixed program bits;
- (L1) margins;
- (L2) wires;
- (L3) complete crossing;
- (L4) a deterministic zone.

The rank field of DR §2.4 is fixed by coordinates at every level. It is a program-like field: `τ_k` contains
only tiles carrying the right bit of the rank. So is the (p4) role pattern of the three encoding zones (DR
Fig. 27): it depends on the row index in the father. All macro-colour bits, including the constant zones,
travel on wires and meet by (M1).

Run the steps with `P^k` an FLEF of `τ_k` on the level-`k` grid. The level-`K` margin at ground level is
`m N_1 ⋯ N_(K−1) >= m`. Step 5 needs `d < N_1 ⋯ N_K` and `m N_1 ⋯ N_(K−1) > d + 2`, both true for large `K`.

**A2. Coordinates stay central (Step 1 with slots).** A diversification slot (DR Fig. 16) is a 2×2 block of
tiles with fake coordinates, framed by 12 skeleton tiles with real coordinates.
- *Off the slots.* Adjacent non-slot faces have coordinate-incrementing edges, and non-slot faces form a
  connected set, since slots are isolated. So Step 1 gives one PVM `C` with
  `C_p(z) = C_(p + z − z')(z')` for all non-slot `z, z'`, commuting with every edge of every non-slot face.
- *Inside a slot.* An edge of a slot face either borders a frame face (an *outer* edge, which commutes with
  `C`) or is one of the four *inner* edges. By A3 the inner edges lie in the algebra of the outer ones, so
  they commute with `C` as well. So `C` is central.

**A3. Slots are classical.**
- *Outer edges.* Frame tiles are skeleton tiles. Their colours facing the slot are those that force the slot's
  pattern, so they are functions of the frame's real coordinates (DR: "only one specific (2×2)-pattern can
  patch it"). On each phase summand the eight outer edges are therefore scalars.
- *Zone windows.* Name the slot tiles BL, BR, TL, TR, with inner edges `v_b` (between BL and BR), `h_l`, `h_r`
  and `v_t`.
  - `v_b` lies in the algebra of the bottom edges of BL and BR. This is the head-crossing rule of Step 2(c):
    a right-moving head is read off BL's bottom and a left-moving head off BR's bottom.
  - `h_l` and `h_r` (the top edges of BL, BR) follow from the other three edges of their faces.
  - `v_t` follows from `h_l, h_r` in the same way as `v_b`.
- *Crossing, fan-out and wire windows (M2).* Inner edges are wire copies of outer edges.

So every edge of a slot is a scalar on each phase summand. Slots then play the role of blank tiles in
Step 2, and Steps 2–5 go through unchanged.

**A4. One-way zones.** Suppose each zone tile's top and right edges are fixed by its bottom and left edges (a
one-way CA). Then Step 2(c) and A3 still hold, by induction on `x + y`.

More generally, suppose every macrotile tile is SW-deterministic: the top and right macro-colours are computed
from the bottom and left ones, and copied out on wires. Then crossing the bottom and left input bits is enough.
Everything else, including the output sides, is a function of those inputs. Such tiles are also
2×2-determinate, so (p2) and part B are unchanged.

## B. Minimality

We follow DR §3.2. Every finite pattern is covered by a 2×2 block `w` of rank-`k` macrotiles for some `k`.
Classify `w` by its position in the father(s) of rank `k + 1`:
1. **Skeleton.** It recurs at the homologous position of every rank-`(k+1)` macrotile.
2. **Exactly one wire, no crossing or fan-out tile.** By (p3) this covers all windows at the margins and
   across the sides of fathers. The wire carries one bit `s` of a rank-`(k+1)` macro-colour. By (p4), for every
   column `i` there are rows `j_0, j_1` in each rank-`(k+2)` macrotile where bit `s` of the top, left and right
   macro-colours is `0`, respectively `1`. So `w` recurs inside every rank-`(k+2)` macrotile. For a window
   across a side, the neighbour at `(i + 1, j_0)` shares that colour.
3. **Touching the zone, a crossing or a fan-out.** `w` is 2×2-determinate: (p2) for the zone, and for (M2)
   because bits pass straight through. Its position and filling have a slot in every rank-`(k+1)` macrotile,
   and the slot reproduces `w` as a pattern of rank-`k` tiles, with the fake coordinates equal to the real
   ones. So its ground-level expansion recurs.
4. **Slot and frame windows.** These are fixed by coordinates and occur in every rank-`(k+1)` macrotile.

In each case `w`, and hence the pattern, occurs in every rank-`(k+2)` macrotile. Every large square contains
one, so `Ω` is minimal.

**Room.** Slots are needed only for case 3:
- DR's `O(m_k^2)` zone windows, with `m_k = poly(log N_k)`, placed in the free stripe above the zone (p1);
- `O(k_r^2)` crossing and fan-out windows, with `k_r = O(log N_(k+1))` the colour length, placed in any
  free region away from wires.
Each slot is `4 × 4`, so the total is `poly(log N_k)`, far below the `N_k^2` space.

## C. Freeness

As in DR §2 (and DRS Prop. 1): every period of a tiling is a multiple of every `N_1 ⋯ N_k`.
