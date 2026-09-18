# Diagonal-time SW layout written out: tile tables, macrotile geometry, causality and crossing checks

Lane bh-g2-fixedpoint-a, 2026-09-18. This is the construction step (§2) of
`sw-minimal-crossing-wire-shift-is-rigid`, written out so that the conditional can be refereed.
- Notation and the four-way layout are from `research/artifacts/gq-bh-g2-fixedpoint-a-crossing-layout.md`,
  cited below as "layout artifact".
- The Durand–Romashchenko construction is arXiv:1802.01461 §2.4, §3.
- Every tile below is SW: its right and top colours are functions of its left and bottom colours. Tiles
  are written `(left, bottom) ↦ (right, top)`.

## 1. Colours and level-1 encoding positions

- **Colours.** A colour is `(coordinate datum, supplementary datum)`.
  - Coordinates follow the layout artifact §1: the left and bottom edges of `(i, j)` carry `(i, j)`.
  - Every tile computes its top coordinate `(i, j+1)` from its **left** edge, and its right coordinate
    `(i+1, j)` from its **bottom** edge.
- **Horizontal side (bottom and top) of a macrotile.** Bit positions lie in `P ⊂ [N/3, 2N/3]`, spaced 3
  apart, in blocks ordered left to right: `P_c` (coordinates), `P_1` (first component), `P_2` (second
  component), `P_f` (the (p4) fields and DR's rank and role fields).
- **Vertical side (left and right).** Heights `Q ⊂ [N/3, 2N/3]`, in blocks ordered bottom to top:
  `Q_c, Q_1, Q_2, Q_f`.
- **Causality (§1 of the claim).** Entry `p` of a top colour may depend on the left colour and on bottom
  entries at positions `<= p`. Entry `q` of a right colour may depend on the bottom colour and on left
  entries at heights `<= q`.

## 2. Tile families

Each row gives `(left, bottom) ↦ (right, top)`. Coordinates are omitted: they always follow §1. `∗` means
blank, and the parenthesis gives the check that the family is causal at level 1.

| family | rule | check |
|---|---|---|
| BLANK | `(∗, ∗) ↦ (∗, ∗)` | trivial |
| V | `(∗, β) ↦ (∗, β)` | same-position copy |
| H | `(β, ∗) ↦ (β, ∗)` | same-height copy |
| CROSS | `(α, β) ↦ (α, β)` | both |
| TURN_LU | `(β, ∗) ↦ (∗, β)` | top from left |
| TURN_BR | `(∗, β) ↦ (β, ∗)` | right from bottom |
| FAN_B | `(∗, β) ↦ (β, β)` | right from bottom, top a copy |
| FAN_L | `(β, ∗) ↦ (β, β)` | top from left, right a copy |
| MERGE | `(β, γ) ↦ ((β, γ), ∗)`, two bits into one pair edge | right from the bottom bit and the same-height left bit |
| END_L, END_B | a wire bit is absorbed; outputs `∗` | trivial |
| COMB_T | `((σ, v), β) ↦ ((σ, v), σ ? v : β)` | top uses the left and the same-position bottom bit |
| COMB_R | `(λ, (σ, v)) ↦ (σ ? v : λ, (σ, v))`, where `λ` is a forwarded bit or pair | right uses the bottom and the same-height left |
| ZT (zone_T cell) | `((a, a'), s) ↦ ((s, a), F(a, a'))` | top from left; right = bottom plus the left's first component, moved from `Q_1` to `Q_2` (up) |
| ZR (zone_R cell) | `(s, (a, a')) ↦ (F'(a, a'), (s, a))` | the transpose; the top's second component moves from `P_1` to `P_2` (right) |
| zone boundary, quiescent | `∅` on outer edges | trivial |
| slot frame and slot | DR §3.2 as SW islands: frame colours are functions of real coordinates, and inner tiles follow ZT/ZR/wire rules with fake coordinates | trivial |

- **Program and start.** Program bits and start states are fixed by coordinates in row 0 of zone_T and
  column 0 of zone_R.
- **Rejection.** A non-accepting final state has no tile, so rejection is enforced by the tile set.

## 3. Zones

- **zone_T** occupies `[a_T, b_T] × [c_T, d_T]`, with `b_T < min P` and `c_T > max Q`, in the upper-left
  ninth.
  - Its row 0 holds copies of all left inputs `Q`.
  - It computes the role, from the coordinates in `Q_c`, and the top colour's `F`-part (layout artifact
    §4 checks).
  - It runs `U` as a one-way CA. The tape drifts right one cell per step, so width `T + S` and height `T`
    suffice for `T` steps in space `S` (standard, recalled). With `y_t(i) = x_t(i+t)`, the ZT rule is a
    radius-1 one-way CA.
- **zone_R** occupies `[a_R, b_R] × [c_R, d_R]`, with `a_R > max P` and `d_R < min Q`, in the lower-right
  ninth. It is the transpose, fed by bottom inputs `P`, and computes the right colour's `G`-part.
- Both zones are `poly(log N) × poly(log N)`.

## 4. Routing (all flows up or right)

- **Bottom input `p ∈ P`.** Column `p` carries `b_p` from `y = 0` up to `h_T(p)`, a private row in
  `[c_T, d_T]` where the tile COMB_T(p) sits. Above it, V carries the output to the top side.
  - At a private height `h_p ∈ [c_R, d_R]`, a FAN_B sends a copy right along row `h_p`.
  - That copy crosses every column `p' > p` and enters zone_R's left boundary.
- **Left input `q ∈ Q`.** Row `q` carries the bit from `x = 0` to a private column `x_q ∈ [a_T, b_T]`,
  where a FAN_L sends a copy up column `x_q` into zone_T's bottom.
  - Row `q` then continues right to COMB_R(q), at a private column `x_R(q) ∈ (b_R, N − m)`. From there an H
    wire runs to the side. On the way to COMB_R(q), row `q` crosses every column
    `p ∈ P` at heights `q < c_T <= h_T(p)`.
  - It meets no zone: `q > d_R` and `q < c_T`.
- **Shifted forwards (ZT, second component).** For the `k`-th height `q_1 ∈ Q_1`, a FAN_L at a private
  column `z_k > max P` sends a copy up to the paired height `q_2 ∈ Q_2`, where a MERGE joins it to row
  `q_2`. So COMB_R(q_2) receives `(straight bit, shifted bit)` as `λ`.
- **zone_T outputs.** From zone_T's right boundary, private rows `h_T(p)` run right to COMB_T(p). Each
  crosses the columns `p' < p` by CROSS tiles: below COMB_T(p') if `h_T(p) < h_T(p')`, otherwise above it.
- **zone_R outputs.** From zone_R's top boundary, the private column `x_R(q)` runs up to COMB_R(q). It crosses the rows
  `q' < q`, which pass it before reaching their own `x_R(q')`, by CROSS tiles.
- **Margins (L1).** The last or first `m` cells of every side wire are straight. Corners are BLANK. The
  COMB tiles sit just inside the margins.

## 5. Checks

- **(L3) complete crossing.**
  - Pairs `p < p'` meet at `(p', h_p)`: the copy of `p`, with `b_(p')` passing through.
  - Pairs `q, p` meet at `(p, q)`.
  - Pairs `q < q'` meet at `(x_q, q')`: column `x_q` runs from `q` up to `c_T`, and row `q'` spans columns
    `[0, x_q]` and beyond.
  - All intersections are distinct CROSS cells. No wire uses another's private row or column.
- **Face-rule reachability (A4).**
  - Every wire, FAN, MERGE and COMB edge is a function of the crossed inputs.
  - ZT and ZR cells are functions of their row 0 or column 0, by induction on `x + y`.
  - Slot and frame edges are coordinate functions.
- **Causality.**
  - Top entry `p` equals `σ ? v : b_p`, with `(σ, v)` from zone_T, which is fed by the left. Its only bottom
    dependence is `b_p`.
  - Right entry `q` equals `σ ? v : λ`, with `(σ, v)` from zone_R, which is fed by the bottom, and `λ` from
    left heights `<= q`, because `q_1 < q_2`.
- **(p1)–(p4) and slots.** Slots sit in free area away from all private lines, and zone windows' slots go
  in the free area near each zone. The (p4) roles are computed by zone_T for top fields and by zone_R for
  right fields.
- **poly(log N) checkability.**
  - Every private line, box and zone corner is an arithmetic expression in `N` and an index of size at
    most `O(log N)`.
  - `ρ_N` is computed as in layout artifact §4, and the tile tables are finite.
  - So DR's fixed-point argument applies with `N_k = 3^(C^k)`.

## 6. Status

- **Written out:** tiles, geometry, crossings and causality.
- **Not re-verified line by line:**
  - that `U` can be run as a one-way CA with drift inside `poly(log N)` zones (standard);
  - that the free area suffices for DR's slot counts (as in the minimal node's "Room" paragraph).
- **To merge:** bh-invent-04's multi-block causal side format, when landed. If it differs, one of the two
  formats should cite the other.
