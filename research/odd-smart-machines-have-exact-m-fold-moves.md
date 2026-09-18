---
rg: 2
id: odd-smart-machines-have-exact-m-fold-moves
kind: claim
title: For every odd m >= 3 an 8-state reversible Turing machine on m letters has SMART's four moves with exact m-fold nesting
distinct_from:
  smart-induced-on-genuine-moves-has-exact-tripling: that is the case m = 3 (SMART itself), after inducing on level-0 moves; this defines one reversible machine for every odd m and proves its move proposition, which specializes at m = 3 to Callard--Salo's Proposition 3.2.
  crossing-move-hierarchies-have-odd-branching: that shows one-head crossing hierarchies can only branch an odd number of times; this realizes every odd branching number m = 2r+1 by an explicit reversible machine.
---

**ESTABLISHED** (lane bh-free-18, elementary lane proof, not reviewed). No priority claimed: two
bounded arXiv API queries (SMART generalizations; Baumslag--Solitar in Brin--Thompson groups) found
nothing. The case `m = 3` is exactly the SMART machine of Cassaigne--Ollinger--Torres-Avilés in the
Kari--Ollinger formalism used by Callard--Salo (arXiv:2208.00685v3, `distortion-1-smart.tex`).

## The machine `SMART_m`

Fix `m = 2r+1 >= 3`. Tape alphabet `Γ = {0, x_1, …, x_r, y_1, …, y_r}` (so `|Γ| = m`), and
`Γ_+ = Γ ∖ {0}`. States `b_i, d_i, p_i, q_i` for `i = 1, 2` (8 states). In the Kari--Ollinger model a
transition is either a move `(q, ±1, q')` or a matching `(q, a, q', a')`.

- **Moves** (phase 2): `(b_2, +1, b_1)`, `(d_2, -1, d_1)`, `(p_2, +1, p_1)`, `(q_2, -1, q_1)`.
- **Matchings** (phase 1), with `1 <= j < r`:

| state | reads `0` | reads `x_j` | reads `x_r` | reads `y_j` | reads `y_r` |
|---|---|---|---|---|---|
| `b_1` | `d_2`, write `x_1` | `q_2`, keep | `q_2`, keep | `q_2`, keep | `q_2`, keep |
| `d_1` | `b_2`, write `x_1` | `p_2`, keep | `p_2`, keep | `p_2`, keep | `p_2`, keep |
| `p_1` | `b_2`, write `y_1` | `d_2`, write `x_{j+1}` | `b_2`, write `0` | `d_2`, write `y_{j+1}` | `q_2`, write `0` |
| `q_1` | `d_2`, write `y_1` | `b_2`, write `x_{j+1}` | `d_2`, write `0` | `b_2`, write `y_{j+1}` | `p_2`, write `0` |

At `m = 3` (`x_1 = 1`, `y_1 = 2`, no `j < r`) this is the SMART table: `b_1: 0|1 → d_2, 1|1, 2|2 → q_2`;
`d_1: 0|1 → b_2, 1|1, 2|2 → p_2`; `p_1: 0|2, 1|0 → b_2, 2|0 → q_2`; `q_1: 0|2, 1|0 → d_2, 2|0 → p_2`.

The table is invariant under the mirror `b ↔ d`, `p ↔ q` with directions reversed.

## Reversibility

The machine is complete and deterministic (each phase-1 state has one matching per letter; each
phase-2 state one move). The reverse machine is also complete and deterministic: each phase-2 state
is entered only by matchings, and each letter is written into it exactly once.
- Into `d_2`: `b_1(0)` writes `x_1`; `p_1(x_j)` writes `x_{j+1}` (`j < r`); `p_1(y_j)` writes `y_{j+1}`
  (`j < r`); `q_1(0)` writes `y_1`; `q_1(x_r)` writes `0`. That is every letter once.
- Into `b_2`: `d_1(0)` writes `x_1`; `q_1(x_j)`, `q_1(y_j)` write `x_{j+1}`, `y_{j+1}`; `p_1(0)` writes
  `y_1`; `p_1(x_r)` writes `0`. Every letter once.
- Into `q_2`: `b_1` keeps each of the `2r` letters of `Γ_+`; `p_1(y_r)` writes `0`. Into `p_2`: `d_1`
  keeps each letter of `Γ_+`; `q_1(y_r)` writes `0`.
Each phase-1 state is entered only by its own move. So `SMART_m` is reversible.

## Proposition (the four moves)

Put `f_m(k) = (2m^{k+1} - (m+1))/(m-1)`, so `f_m(0) = 1`, `f_m(k+1) = m f_m(k) + m + 1`, and
`f_3(k) = 3^{k+1} - 2`. For all `k >= 0`, `s_+ ∈ Γ_+`, `s_* ∈ Γ`:
- `M_b(k)`: on `s_+ 0^k s_*` with `b_2` on `s_+`, after `f_m(k)` steps `b_1` is on `s_*`.
- `M_d(k)`: on `s_* 0^k s_+` with `d_2` on `s_+`, after `f_m(k)` steps `d_1` is on `s_*`.
- `M_p(k)`: on `s_* 0^k s_+` with `p_2` on `s_*`, after `f_m(k)` steps `p_1` is on `s_+`.
- `M_q(k)`: on `s_+ 0^k s_*` with `q_2` on `s_*`, after `f_m(k)` steps `q_1` is on `s_+`.

In each move the head stays in the displayed domain, the tape is the same at the end, the cell of
`s_+` is never modified, and the cell of `s_*` is visited only at the last step (`b`, `d`) or only at
the first step (`p`, `q`).

**Proof.** `k = 0` is one move transition. For `k+1`, write `e` for the extra cell, which starts as `0`.
By the mirror symmetry it suffices to treat `b` and `p`.
- `M_b(k+1)` on `s_+ 0^k e s_*`: `M_b(k)` on `s_+ 0^k e` (with `e` as its `s_*`) ends with `b_1` on `e = 0`,
  which writes `x_1` and gives `d_2`. Then, for `j = 1, …, r`: `M_d(k)` on `s_+ 0^k e` (with `e = x_j` as its
  `s_+`, `s_+` as its `s_*`) ends with `d_1` on `s_+ ∈ Γ_+`, which keeps it and gives `p_2`; `M_p(k)` on the
  same domain ends with `p_1` on `e = x_j`, which writes `x_{j+1}` and gives `d_2` if `j < r`, or writes `0`
  and gives `b_2` if `j = r`. Finally `b_2` moves onto `s_*` as `b_1`.
- `M_p(k+1)` on `s_* e 0^k s_+`: `p_2` moves onto `e = 0`; `p_1` writes `y_1` and gives `b_2`. Then, for
  `j = 1, …, r`: `M_b(k)` on `e 0^k s_+` (with `e = y_j` as its `s_+`) ends with `b_1` on `s_+`, which keeps
  it and gives `q_2`; `M_q(k)` on `e 0^k s_+` ends with `q_1` on `e = y_j`, which writes `y_{j+1}` and gives
  `b_2` if `j < r`, or writes `0` and gives `p_2` if `j = r`. Finally `M_p(k)` on `e 0^k s_+` (with `e = 0`
  as its `s_*`) ends with `p_1` on `s_+`.

The sub-moves apply by induction, because `e` is a boundary cell of each sub-move that the sub-move
never modifies (as `s_+`) or reaches only at its last or first step (as `s_*`), and every value it
takes as an `s_+` is nonzero. Each level-`(k+1)` move is `m` sub-moves and `m+1` junction steps, so
`f_m(k+1) = m f_m(k) + m + 1`. The remaining assertions follow from the induction hypothesis. ∎

## The nesting and its boundary values

The sub-move types form a constant-length-`m` substitution:
`b → b (d p)^r`, `d → d (b q)^r`, `p → (b q)^r p`, `q → (d p)^r q`. In a `b` or `q` parent the extra cell is
right of the sub-domain; in a `d` or `p` parent it is left. The sub-moves' boundary pairs `(s_+, s_*)`
do not depend on `k`:
- in `M_b`: `b` has `(s_+, 0)`, then `d_j` and `p_j` have `(x_j, s_+)`;
- in `M_p`: `b_j` and `q_j` have `(y_j, s_+)`, then `p` has `(s_+, 0)`;
- `M_d`, `M_q` are the mirrors (`d` has `(s_+, 0)`, `b_j, q_j` have `(x_j, s_+)`; `d_j, p_j` have `(y_j, s_+)`,
  then `q` has `(s_+, 0)`).

**Parent table.** A sub-move of type `t` with boundary `(σ_+, σ_*)` determines its parent and index:
if `σ_* = 0`, the parent has type `t` and the sub-move is its first (`b`, `d`) or last (`p`, `q`) one; if
`σ_* ≠ 0`, then `σ_+ = x_j` or `y_j` fixes the parent (`b` in a `d` or `p` parent, `d` in a `b` or `q`
parent, `p` in a `b` or `q` parent, `q` in a `d` or `p` parent) and the index. The last sub-move of `b`
and `p` is `p`; of `d` and `q` it is `q`. Moves of type `b` or `d` are never last sub-moves.

Consumed by `odd-smart-induced-map-has-height-m-renormalization`.
