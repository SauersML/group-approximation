# Adversarial check: `BS(1,m) ≤ 3V` for every odd `m` (bh-refute, 2026-09-18)

This is an independent red-team verification, by hand with no computation, of bh-free-18's chain:
`odd-smart-machines-have-exact-m-fold-moves`, then `odd-smart-induced-map-has-height-m-renormalization`,
then `bs-1-m-embeds-in-brin-thompson-3v-for-odd-m`.
Verdict: **PASS**. No gap was found in the `m`-dependent steps. The steps that are word-for-word the refereed
`m = 3` argument were not re-derived: the one-level-less Lemma's induction scheme, the density argument of
case 2, and the first-return and renormalization imports.

## 1. The move proposition, fully re-derived

Set `m = 2r+1`. I re-ran the induction for `M_b(k+1)` on `s_+ 0^k e s_*` from the table:
- `M_b(k)` leaves `b_1` on `e = 0`, which writes `x_1` and gives `d_2`.
- For `j = 1..r`:
  - `M_d(k)`: its `s_+` is `e = x_j`, which is nonzero, and its `s_*` is the original `s_+`. It ends with `d_1` on the
    original `s_+`, which is kept and gives `p_2`.
  - `M_p(k)` ends with `p_1` on `e = x_j`, which writes `x_{j+1}` and gives `d_2` (for `j < r`), or writes `0` and gives
    `b_2` (for `j = r`).
- Finally `b_2` moves onto `s_*` as `b_1`.
- The original `s_+` is only read and kept; `e` is restored to `0`; `s_*` is touched only at the last step.
- Count: `f + 1 + r(2f + 2) + 1 = m f + m + 1`.

I did the same for `M_p(k+1)` on `s_* e 0^k s_+`:
- `p_2` moves onto `e`, and `p_1` writes `y_1` and gives `b_2`.
- For each `j`: `M_b(k)` with `s_+ = y_j` ends with `b_1` on the original `s_+`, which is kept and gives `q_2`. Then `M_q(k)` ends
  with `q_1` on `y_j`, which gives `b_2` and writes `y_{j+1}` (for `j < r`), or gives `p_2` and writes `0`.
- Then `M_p(k)` with `e = 0` as its `s_*`.
- Count: `m f + m + 1`.

The table is invariant under `b ↔ d`, `p ↔ q` with directions reversed (checked row by row), so the
`d` and `q` moves follow. The reversibility bookkeeping (each phase-2 state entered by each letter
exactly once) is correct.

## 2. The m-dependent renormalization inputs

- **Entry into `Y` within 5 steps, and `r_Y <= 6`.** Re-derived for:
  - `b_2` on `0` (both neighbour cases);
  - `p_2` with right neighbour `0`;
  - phase-1 configurations;
  - the mirrors.
- **Exact count `m^k`.** Every phase-2 configuration inside a move is either the start of a level-0 move, and
  so lies in `Y`, or one of the two junction configurations. The two junctions are `b_2` on the reset cell,
  which is `0`, and the leading `p_2` with right neighbour `0`, and neither lies in `Y`. The case `k = 0` of
  `M_p` was checked separately: there `p_2` has nonzero right neighbour, so it is a genuine start.
- **Parent table.** It is unambiguous:
  - `σ_* = 0` forces the first (`b`, `d`) or last (`p`, `q`) sub-move of a same-type parent;
  - `σ_* ≠ 0` reads the parent and the index `2j−1` or `2j−2` off `σ_+ ∈ {x_j, y_j}`.
  So `i_0` is locally constant and advances by 1 mod `m` along `U`.
- **Rows are local.** A `b_2`-point has `i_0 = 0` exactly when its right neighbour is `0` (the first sub-move of a
  `b` parent), or when it sits on `y_1` with a nonzero right neighbour (index 0 of a `p` parent). Every other
  `b_2`-point has index `2j−1` or `2j−2 >= 1`. The mirrors hold for `d_2`.
- **The `φ` table at level 1.** Rows `b` and `p` were checked against the first `Y`-points of `M_b(1)` and `M_p(1)`
  and of `M_b(0)` and `M_p(0)`. The edits are deleting the `0` beside the head, and deleting the head cell with
  the head moved and the state set to `p_2`. Their inverses land in `A` by the parent table.
- **`F ∈ 2V` for alphabet size `m`.** A complete binary prefix code on `m` letters exists for every `m`, so the
  moving-tape map is a brick map as for `m = 3`.

## 3. Attacks tried (all failed)

- **Stray `Y`-points from junction phase-2 configurations.** None found, including at `k = 0`, which is the
  only place a junction and a genuine start could coincide.
- **Ambiguity of the parent for `b_2` on `x_1` next to a `0`.** It is resolved by `σ_* = 0`, which forces a `b` parent.
- **Even `m`.** Not claimed. The alternation `x`/`y` of the extra cell needs `m − 1 = 2r` letter values, and the
  node's odd-branching caveat stands.

## Priority

There is none beyond the node's own bounded arXiv search. The `m = 3` case is the refereed swarm result
(`bs13-embeds-in-brin-thompson-3v`). The optional MSI whole-tape check of `φ U^m = U φ` at `m = 5`
suggested on the node would be an independent numerical confirmation. It is not needed for this check.
