# Referee report (gq-referee-a, proof-gap lens): SMART induced on level-0 configurations factors onto Z/2 × Z_3

**Reviewed:** lane gq-nv-obstruct, 37c1222a1, read on origin/main.
- `smart-level-zero-return-map-factors-onto-3-adic-odometer`, with the proof in
  `research/artifacts/gq-gq-nv-obstruct-smart-odometer.md`;
- the route `odometer-factor-via-smart-level-zero-return-map`;
- checked against the Callard–Salo source `distortion-1-smart.tex`: the table, l. 2–35; `prop:smart-moves` and its
  proof, l. 52–214; the level Claim, l. 455–475. The source is kept in the lane scratch `$GQ/src/callard-salo/`.

**Verdict: PASS**, subject to the minimality citation in §6 (for referee-b). I found no proof gap. Two write-up
fixes are listed in §7. If the citation holds, the hole `some-brin-thompson-element-factors-onto-an-odometer` is
answered YES, with `k = 2`, `m = 3`.

## 1. The substitution (coordinator (1))
I re-ran the proof of `prop:smart-moves` from the table. In the Kari–Ollinger model a symbol transition does not
move the head.
- **`M_b(k+1)`** on `(s_+ 0^k 0 s_*)`, starting with `b_2` on `s_+`:
  - `M_b(k)` on `(s_+ 0^k [0])`;
  - `b_1: 0|1 → d_2`;
  - `M_d(k)`, with `s'_+` the new 1 and `s'_* = s_+`;
  - `d_1: s_+|s_+ → p_2`;
  - `M_p(k)`, with `s'_* = s_+` and `s'_+` the 1;
  - `p_1: 1|0 → b_2`;
  - `b_2 ▶ b_1` onto `s_*`.
  - So the sub-move sequence is `b → bdp`, followed by two trailing configurations.
- **`M_p(k+1)`** on `(s_* 0 0^k s_+)`, starting with `p_2` on `s_*`:
  - `p_2 ▶ p_1`;
  - `p_1: 0|2 → b_2`;
  - `M_b(k)` on `([2] 0^k s_+)`;
  - `b_1: s_+|s_+ → q_2`;
  - `M_q(k)`, with `s'_+` the 2;
  - `q_1: 2|0 → p_2`;
  - `M_p(k)` on `([0] 0^k s_+)`.
  - So `p → bqp`, preceded by two leading configurations.
- **Mirror symmetry.** The table is invariant under `b↔d`, `p↔q` together with left–right reflection. I checked
  all eight arrows. This gives `d → dbq` and `q → dpq`.
- **Recursion checks.** The configurations of a level-`(k+1)` move are those of its three sub-moves plus exactly
  two special ones, so `f(k+1)+1 = 3(f(k)+1)+2`. This agrees with `f(k) = 3^{k+1} − 2` and with
  `f(k+1) = 3f(k)+4`.
- **The ends of a sub-move are never modified during it.** `s_+` is never modified, and `s_*` is touched only by a
  move transition, as the head arrives in `b/d` or leaves in `p/q`.

## 2. `Y` is clopen and radius-1 (coordinator (2))
- **The eight patterns.**

  | state | condition |
  |---|---|
  | `b_2` at `i` | `c_i ∈ {1,2}` |
  | `b_1` at `i` | `c_{i−1} ∈ {1,2}` |
  | `d_2` at `i` | `c_i ∈ {1,2}` |
  | `d_1` at `i` | `c_{i+1} ∈ {1,2}` |
  | `p_2` at `i` | `c_{i+1} ∈ {1,2}` |
  | `p_1` at `i` | `c_i ∈ {1,2}` |
  | `q_2` at `i` | `c_{i−1} ∈ {1,2}` |
  | `q_1` at `i` | `c_i ∈ {1,2}` |

- **Why the end patterns are genuine.** `x_1` is entered only through the move `x_2 → x_1`. So an end pattern has
  the right predecessor, and that predecessor is the start of an `M_x(0)`.
- **Start and end are disjoint.** Starts use `_2` states and ends use `_1` states. So `pos_0 = j_0` is well
  defined.

## 3. Specials are never level-0, so `L(k) = 2·3^k` (coordinator (3))
- **The four special configurations.** For `k+1 ≥ 1`:
  - the trailing specials of `M_b(k+1)` are `b_2` on the restored `0` and `b_1` on `s_*` with a `0` to its left;
  - the leading specials of `M_p(k+1)` are `p_2` on `s_*` with a `0` to its right, and `p_1` on a `0`;
  - `d` and `q` are the mirrors.
- **None is in `Y`.** Each of the eight patterns in §2 requires a nonzero cell exactly where these configurations
  have a `0`. This agrees with the source Claim's "disjointly cover".
- **Consequence.** `L(0) = 2` and `L(k+1) = 3L(k)`.

## 4. The parent table on Z-tapes (the author's (1), coordinator (4))
- **Occurrences of each type as a sub-move.** Read off the substitution:

  | type | as a sub-move of |
  |---|---|
  | `b` | `b` at index 0 with `s_* = 0`; `d` at index 1 with `s_+ = 1`, `s_* ≠ 0`; `p` at index 0 with `s_+ = 2`, `s_* ≠ 0` |
  | `d` | mirror of `b` |
  | `p` | `b` at index 2 with `s_+ = 1`, `s_* ≠ 0`; `p` at index 2 with `s_* = 0`; `q` at index 1 with `s_+ = 2`, `s_* ≠ 0` |
  | `q` | mirror of `p` |

  - These are the sub-move's own end values during the sub-move: the written `1` or `2` is its `s_+`, and the old
    `s_+` or the restored `0` is its `s_*`.
- **The table matches.** This is exactly the artifact's table.
- **It is exhaustive.** The three columns partition `{1,2} × {0,1,2}`, and each type occurs exactly once per column.
- **Genuineness on Z.**
  - In each case the parent's domain is the sub-move's domain plus one cell. That cell is the parent's `s_*`,
    which may hold any value. The parent's `s_+` is either the sub-move's `s_+` or its nonzero `s_*`, so it lies
    in `{1,2}` as required.
  - I checked this against the tape at the time of the sub-move, including the written `1` or `2`.
  - On `Z` that extra cell always exists, and `F` is a homeomorphism. So the actual orbit runs the parent both
    forward and backward.
  - A table entry is unique, so the canonical parent is the only genuine level-`(k+1)` move containing the
    sub-move.
- **Locality.** The values of `s_+` and `s_*` for every level `j < k` are present on the tape at time `y`.
  - So `pos_k` is a function of the state and the cells within distance `k+1` of the head.
  - The position of the domain relative to the head varies with `y`. Say "cells within distance `k+1`" rather
    than "the `k+2` cells".

## 5. Equivariance and the factor (the author's (3))
- **Inside a move.** Let `M` be `y`'s level-`k` move. Every configuration in the time interval of `M` belongs to
  `M`. Its `Y`-configurations are exactly the level-0 configurations of `M`. So `F_Y y` is the next of these,
  `M` is its canonical move (by uniqueness), and `pos_k` goes up by 1.
- **At a boundary.** Let `M'` be the canonical move of `F_Y y`.
  - `M'` does not contain `y`'s time. Otherwise `y`, which lies in `Y`, would be in a level-0 sub-move of `M'`,
    and uniqueness would give `M' = M`.
  - So `M'` lies after `y`, and its level-0 configurations before `F_Y y` would be returns to `Y` strictly between
    `y` and `F_Y y`. Hence `pos_k(F_Y y) = 0`.
  - This needs only that `M'` does not contain `y`. The general disjointness claim is not needed.
- **The factor.**
  - `pos_{k+1} = i_k·2·3^k + pos_k`, so `π = (pos_k)_k` lands in `lim Z/(2·3^k) ≅ Z/2 × Z_3`. It is continuous
    and satisfies `π∘F_Y = π + 1`.
  - `F_Y` is a bijection of `Y`, so `π(Y)` is closed and `+1`-invariant. `+1` is minimal, so `π` is onto.
  - The projection to `Z_3` sends `1` to `1`.

## 6. The 2V conjugation (the author's (4)) and the one citation dependency
- **The first-return lemma.** `brin-thompson-first-return-maps-lie-in-kv-proof` is correct as written.
  - The pieces `Y_r` are clopen, and `T_Y = T^r` on `Y_r`.
  - For injectivity and surjectivity, compare the two return times `r ≤ s` and use minimality of the return time.
  - `ψ` is built from brick partitions of `Y` and of `C^k` with equally many pieces.
  - A composite of three maps, each canonical on a finite brick partition, is again in `kV`.
- **Coding.** Callard–Salo's machine has **8** states. The proof of `three-v-contains-aperiodic-rationals` item 1
  codes 4 states with `β: Q → {00, 01, 10, 11}`. Its argument is general (the moving-tape model, prefix codes),
  and works verbatim with any complete prefix code of size 8. State this.
- **Minimality is cited, not proved.** Bounded returns (`C^2 = ∪_{i ≤ R} T^{-i}Y'`) come from minimality of `F`.
  - Callard–Salo §1 (`distortion-0-main.tex` l. 360) says their `𝒮` "is reversible and aperiodic, and whose
    moving-tape dynamics is a minimal homeomorphism", citing Cassaigne–Ollinger–Torres-Avilés and Ollinger's
    2018 talk. They use `𝒮` for the 8-state Kari–Ollinger version of §2, which their Remark calls "in a sense
    completely equivalent" to the original.
  - Whether minimality transfers to this duplicated-state version is a citation question for gq-referee-b.
  - A direct proof looks available, which would remove the dependency. On finite-level chains, at most 4 special
    configurations are consecutive, because `b` and `d` are never the last sub-move. On `Z` the level-`∞`
    specials should enter `Y` within a few steps. I checked one case: `b_2` on `0` with zeros to the left reaches
    `M_d(0)` or `M_q(∞) → M_d(0)` within 4 steps. The other seven were not checked.

## 7. Write-up fixes (non-blocking)
1. Use a size-8 state code in the 2V coding (§6).
2. For the locality of `pos_k`, say "cells within distance `k+1` of the head", because the domain's position
   depends on `y` (§4).
