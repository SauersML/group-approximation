# Crossing-wire layout written out: tiles, zone encoding, poly(log N) checkability

Lane bh-g2-fixedpoint-a, 2026-09-18. This is the construction step of
`crossing-wire-fixed-point-tile-sets-are-quantum-rigid` (conditions (L0)–(L4)) and of
`minimal-crossing-wire-fixed-point-shift-is-quantum-rigid` ((M1)–(M3)), written out as the referee asked
(bh-ref-engines, 11493c386).

DRS is arXiv:0910.2415 §2.2–2.3; DR is arXiv:1802.01461 §2.4, §3. Both were read at source. DRS assume
wires do not cross and encode the zone with window tiles. Both choices are replaced here, and §4 checks
that the fixed-point argument is unaffected.

## 1. Colours and roles

- A colour is a pair `(coordinate datum, supplementary datum)`. Following DR §2.4:
  - the left and bottom edges of the tile at `(i, j)` carry `(i, j)`;
  - the right edge carries `(i+1 mod N, j)`;
  - the top edge carries `(i, j+1 mod N)`.
- Supplementary data come from `Σ = {∗} ⊔ {0,1} ⊔ Σ_zone`, where `∗` means blank. `Σ_zone` is defined in §3.
- A *role map* `ρ_N : [0,N)^2 → Roles` fixes, from the coordinates alone, which of the finite tile families
  below may sit at `(i, j)`. The tile set `τ` is the union, over positions, of the families allowed there.

## 2. Wire tiles and the crossing box

Each item lists the supplementary data on (left, right, bottom, top); unlisted edges are `∗`, and
`β, α ∈ {0,1}`.

| role | tiles |
|---|---|
| BLANK | all `∗` |
| BIT(side) at a bit position of a side | the outer edge and the inner edge on the same axis carry `β` |
| H (horizontal wire) | `(β, β, ∗, ∗)` |
| V (vertical wire) | `(∗, ∗, β, β)` |
| TURN (e.g. enters right, leaves down) | right `β`, bottom `β` |
| CROSS | `(α, α, β, β)`, all four `(α, β)` |
| FAN (vertical in, copy to the right) | `(∗, β, β, β)` |
| END (row copy terminates) | `(β, ∗, ∗, ∗)` |

**Inputs.** Let `K = 4k` be the number of bit positions on the four sides, and index them `q = 1, …, K`.
- Bit positions sit in the middle of each side, spaced 3 apart. For DR (p3), wires are spaced `>= 3` apart
  outside the box.
- Left-side bits sit one row above the right-side bits, and top-side bits one column right of the bottom-side
  bits, so no two sides share a row or column.
- Wire `q` leaves its side perpendicularly and runs straight for `m` cells (the margin (L1)). It is then
  routed along segments on its own private rows and columns. These are all distinct, spaced 3 apart, outside
  the margins, the box and the zone.
- The last segment is column `c_q`, going up into the box from below.
- Consequences of the routing:
  - distinct wires meet only where a private row of one crosses a private column of another, and those
    cells are CROSS tiles;
  - a TURN sits at the intersection of two of the wire's own private lines, which no other wire uses;
  - the only other thing inside a margin is that side's own bit wires.

**The crossing box `[X_0, X_0 + 2K + 1] × [Y_0, Y_0 + 2K]`.** (Widened by one column after bh-free-35 (f757d5cbc) found that the END column coincided with the last wire column `c_K = X_0 + 2K`.) Wire `q` enters at the bottom in column
`c_q = X_0 + 2q`, going up, and leaves at the top towards the zone. Put `r_q = Y_0 + 2q`.

| cell | role |
|---|---|
| `(c_q, r_q)` | FAN: a copy of bit `q` starts to the right along row `r_q` |
| `(c_q, r_(q'))` with `q' < q` | CROSS: horizontal bit `q'`, vertical bit `q` |
| `(c_(q'), r_q)` with `q' < q` | V (the row copy of `q` starts at `c_q`, to the right) |
| `(x, r_q)` with `c_q < x < X_0 + 2K + 1`, `x` not a column | H |
| `(X_0 + 2K + 1, r_q)` | END |
| other box cells | BLANK |

So every pair `q' < q` meets in the CROSS tile at `(c_q, r_(q'))`. That is (L3).

## 3. The zone: a one-head tableau with head edges (L4)

`U` is DRS's universal machine, with states `Q`, accepting state `q_acc` and tape alphabet `Γ`. A cell symbol
is `a = (π, w)`, where `π` is the read-only program bit and `w ∈ Γ`. Put
`Σ_zone = Γ' ∪ (Q × Γ') ∪ {none, →q, ←q : q ∈ Q}`, where `Γ'` is the set of cell symbols. Horizontal edges carry a
cell content and vertical edges carry a head message.

At the zone cell `(x, t)`, with (left, right, bottom, top):

| type | tile |
|---|---|
| (a) no head | `(none, none, a, a)` |
| (b) head arrives from the left | `(→q, none, a, (q, a))` |
| (c) head arrives from the right | `(none, ←q, a, (q, a))` |
| (d) `δ(q, a) = (q', a', R)` | `(none, →q', (q, a), a')` |
| (e) `δ(q, a) = (q', a', L)` | `(←q', none, (q, a), a')` |
| (f) accept | `(none, none, (q_acc, a), (q_acc, a))` |

- There is no tile with two incoming heads, and no tile for a non-accepting halt.
- Program bits: at column `x` the only allowed symbols are those with `π = π_x`. That is (L0).
- Boundaries: the boundary columns have outer vertical edges `none`, and there are no (d)/(e) tiles pointing
  outward.
- Row `0`: bottom edges are input wires at the input columns, a fixed blank symbol elsewhere, and the start
  head `(q_0, a_0)` at `x_0`. All of this is fixed by coordinates.
- Top row: tiles exist only for bottoms that are head-free or carry `q_acc`, and their top edges are `∗`.

**The facts Step 2(c) uses.**
- The right edge is `→q'` only in (d), so its `→`-part is a function of the bottom.
- The left edge is `←q'` only in (e), so its `←`-part is a function of the bottom.
- The top is a function of the other three edges.

## 4. Coordinate-fixed rules, poly(log N) checkability, and the fixed point

- `ρ_N(i, j)` compares `(i, j)` with `O(K) = O(log N)` numbers: the side bit positions, `R_q`, `C_q`, `c_q`,
  `r_q`, the box corners and the zone rectangle. Each number is an arithmetic expression in `N` and `q`, so
  `ρ_N` takes `poly(log N)` time.
- Membership of a colour quadruple in `τ` is checked as follows:
  - read `(i, j)` and check the coordinate increments, in `O(log N)`;
  - compute `ρ_N(i, j)`;
  - look up the supplementary data in the finite table of that role. The zone table uses the fixed finite
    `δ` of `U`, and the program role needs bit `π_x` of the program's own text, which is DRS's
    self-reference.
- This is the kind of check DRS §2.3 requires ("simple things only … polynomial in the input size, which is
  `O(log N)`"). So their Kleene fixed-point construction yields a self-simulating `τ` with this layout for all
  large `N`.
- In DR's variable-zoom version the same holds with `N_k`, computed from `k` in `poly(log N_k)` time.
  Diversification slots, and slots for CROSS/FAN windows (M2), are further coordinate-fixed roles whose
  frame colours are functions of the coordinates.

## 5. Where each rigidity step uses the layout

- (L0) and Step 1: coordinate increments across every edge off the slots.
- (L1): the first `m` cells of each wire are straight, and corners are BLANK.
- (L2) and Step 2(b): the H, V, TURN, FAN, END and BIT tiles copy one bit.
- (L3) and Step 2(a): the box table above.
- (L4) and Step 2(c): the zone table above.
