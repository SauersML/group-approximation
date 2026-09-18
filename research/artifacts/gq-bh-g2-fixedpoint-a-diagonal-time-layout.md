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
  apart, in blocks ordered left to right: `P_c` (coordinates), `P_1, P_2, P_3` (first, second, third
  components), `P_f` (the (p4) fields and DR's rank and role fields).
- **Vertical side (left and right).** Heights `Q ⊂ [N/3, 2N/3]`, in blocks ordered bottom to top:
  `Q_c, Q_1, Q_2, Q_3, Q_f`.
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
| ZT (zone_T cell, §7) | `((a_1, a_2, a_3), s) ↦ ((s, a_1, a_2), F_U(a_3, a_2, a_1))` | top from left; right = bottom plus the left's components shifted up (`Q_1 → Q_2 → Q_3`) |
| ZR (zone_R cell, §7) | `(s, (b_1, b_2, b_3)) ↦ (F_U(b_3, b_2, b_1), (s, b_1, b_2))` | the transpose; the top's components shift right (`P_1 → P_2 → P_3`) |
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
  - It runs `U` as the drift-2 tableau of §7: width `S + 2T` and height `T` for `T` steps in space `S`.
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
  - (closed in §7) running `U` in the zones: an explicit drift-2 tableau, not a general one-way-CA citation;
  - (closed in §8) free area for slots: an explicit count, and the upper-right ninth is free.
- **To merge:** bh-invent-04's multi-block causal side format, when landed. If it differs, one of the two
  formats should cite the other.

## 7. The zone: a one-head TM on a drift-2 diagonal (closes §6, first point)

`U` is DRS's universal machine: states `Q ∋ q_0, q_acc`, cell symbols `Γ'` (with the read-only program bit),
transitions `δ(q, a) = (q', a', D)` with `D ∈ {L, R}`, and `q_acc` halting. Contents are
`C = Γ' ∪ (Q × Γ') ∪ {∅}`, where `∅` means outside the tape.

**Placement.** Tape cell `c` at time `t` sits in zone column `x_0 + c + 2t`, row `t`.
- In one step the head moves from column `x_0 + c + 2t` to `x_0 + c ± 1 + 2t + 2`, that is by `+1` or `+3`.
  So the head only moves right.
- The new content of cell `c`, in column `y = x_0 + c + 2t + 2`, depends on the old contents of cells
  `c − 1, c, c + 1`. Those sit in columns `y − 3, y − 2, y − 1`, all to the left in row `t`.

**The ZT family.**

| edge | colour |
|---|---|
| bottom | `s ∈ C`, the content of this column at time `t` |
| left | `(a_1, a_2, a_3)`, the contents of columns `y − 1, y − 2, y − 3` in row `t` |
| right | `(s, a_1, a_2)` |
| top | `F_U(a_3, a_2, a_1)` |

The right edge is a relay window of depth 3. The top is the local update `F_U(l, m, r)`:
- `m = (q, a)` with `δ(q, a) = (q', a', D)` gives `a'`;
- `m = a` and `l = (q, b)` with `δ(q, b) = (q', ·, R)` gives `(q', a)`;
- `m = a` and `r = (q, b)` with `δ(q, b) = (q', ·, L)` gives `(q', a)`;
- `m = (q_acc, a)` gives `(q_acc, a)`;
- otherwise `m = a` gives `a`, and `∅` gives `∅`.

There is **no tile** for two converging heads, or for a halting state other than `q_acc`, so rejection is
enforced.

**Boundary and rows.**
- Row 0 holds the inputs (wire copies) and the program bits, fixed by coordinates, at columns
  `x_0 + c`. The start head `(q_0, a)` is at `x_0`, and blanks and `∅` fill the rest.
- The zone's left boundary edges are `(∅, ∅, ∅)`. Cells never move left of cell 0, since the tape region in
  row `t` is `[x_0 + 2t, x_0 + 2t + S)`.
- In the last row `T` only tiles whose `F_U`-value is head-free or `q_acc` exist. Output wires leave the top
  at the output cells' columns `x_0 + 2T + c` and go up and right.
- Size: width `S + 2T + 3`, height `T`, which is `poly(log N_k)` for DRS's checks.

**Checks.**
- SW: the tile is fixed by its left and bottom edges.
- Causality at level 1:
  - the top depends on the left only;
  - the right's first component is the bottom;
  - the right's second and third components come from the left's first and second, moved up
    `Q_1 → Q_2 → Q_3`.
- Face-rule reachability: by induction on `x + y` from row 0 and the left boundary.

**ZR** is the transpose: time runs rightward, the tape drifts up 2 per column, and the right edge equals
`F_U(b_3, b_2, b_1)` read from the bottom window.

## 8. Free area at level `k` (closes §6, second point)

Measure a rank-`k` macrotile in rank-`(k−1)` tiles, side `N = N_k`. Let `K = O(log N_(k+1)) = O(C log N)` be
the number of side bits, since `N_(k+1) = N^C`.
- **Wires**, counting widths and the spacing gap 3: side runs, private rows and columns, the long crossing
  copies, fan-out columns `z_k`, and the zone output rows and columns. That is at most `8K` lines, each of
  length at most `N`. Area `<= 32 K N = O(N log N)`.
- **Zones** zone_T and zone_R: `2 (S + 2T + 3) T = poly(log N)`.
- **Slots.**
  - Zone windows: at most `4 · poly(log N)` positions times `|C|^4` fillings.
  - Crossing, fan, merge and COMB windows: `O(K^2)` positions times at most 16 fillings.
  - Each slot with its frame and a gap needs a `7 × 7` block.
  - Total `poly(log N)`.
- **Free region.** No private line enters the upper-right ninth `R_free = [2N/3 + 3, N − m − 3]^2`:
  - top outputs use columns `P ⊂ [N/3, 2N/3]`, and right outputs use rows `Q ⊂ [N/3, 2N/3]`;
  - zone_T and zone_R are in the upper-left and lower-right ninths;
  - bottom copies run at heights `< N/3`, zone_T output rows at columns `< 2N/3`, and zone_R output
    columns at heights `<= 2N/3`;
  - the shifted-forward columns run at heights `<= 2N/3`.

  So `R_free` is blank and has area `(N/3 − m − 6)^2 >= N^2/10` for large `N`. All `poly(log N)` slots fit
  there, pairwise separated, at distance `>= 3` from every wire and zone.
- **Free fraction.** At least `1 − O(log N / N) → 1` of the macrotile is blank. That exceeds DR's (p1) need
  (free area of linear size near the zone), since slots need no vertical alignment here.

## 9. Lesson for general BH

A self-simulating deterministic tiling can compute universally without any backward signal. Let the tape
drift faster than the head (drift 2 against head speed 1). Every dependency then points backward in space,
and causality becomes a matter of geometry, not of the machine.
