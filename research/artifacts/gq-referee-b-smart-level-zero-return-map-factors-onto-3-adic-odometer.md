# Referee report (citation/hypothesis lens): `smart-level-zero-return-map-factors-onto-3-adic-odometer` and route `odometer-factor-via-smart-level-zero-return-map`

Referee: lane gq-referee-b, 2026-09-17. Reviewed:
- the claim and route as landed at 37c1222a1;
- the proof artifact `research/artifacts/gq-gq-nv-obstruct-smart-odometer.md`.

Source: Callard–Salo, arXiv:2208.00685v3, e-print `distortion-1-smart.tex`, read locally.

## Verdict

**PASS.** Every use of the Callard–Salo text matches the source. I re-derived the recursions, the case table and the
counting. The two cited repo nodes apply with their hypotheses met. One trust surface is minimality (T1), and one
note concerns novelty (N1).

## (1) Transition table (l. 2–35). Matches.

Checked arrow by arrow against the TikZ source:
- **Moves:** `b_2 ▶ b_1`, `d_2 ◀ d_1`, `p_2 ▶ p_1`, `q_2 ◀ q_1`.
- **`b_1`:** `0|1 → d_2`; `1|1, 2|2 → q_2`.
- **`d_1`:** `0|1 → b_2`; `1|1, 2|2 → p_2`.
- **`p_1`:** `0|2, 1|0 → b_2`; `2|0 → q_2`.
- **`q_1`:** `0|2, 1|0 → d_2`; `2|0 → p_2`.
- **Filled/hollow (l. 37):** `b, d` are filled; `p, q` are hollow.

## (2) `prop:smart-moves` (l. 52–97). Matches and holds.

- **Verbatim.** The statement reads: "For all k, s_* ∈ {0,1,2} and s_+ ∈ {1,2} … Additionally, the cell
  containing s_* is only visited at the last (resp. first) step of … M_b and M_d (resp. M_p and M_q). And the
  cell containing s_+ is never modified."
- **Base case.** `k = 0` is one move transition for each `x`.
- **`M_b(k+1)` induction.** Every sub-move is applied with admissible roles:
  - `M_b(k)` on `(s_+ 0^k 0)` with sub-`s_* = 0`;
  - `b_1: 0|1 → d_2`;
  - `M_d(k)` with sub-`s_+ = 1` and sub-`s_* =` the parent's `s_+`;
  - `d_1` reads `s_+ ∈ {1,2}` and writes it back unchanged;
  - `M_p(k)` with sub-`s_* =` the parent's `s_+` and sub-`s_+ = 1`;
  - then `p_1: 1|0 → b_2`, and `b_2 ▶`.
- **`M_p(k+1)` induction.** Checked the same way.
- **The "additionally" clauses.** They hold because sub-moves never leave their domains, and the parent's `s_+`
  is read only through the `1|1, 2|2` transitions.
- **The mirror symmetry.** Reflecting the tape and swapping `b↔d`, `p↔q` maps the table onto itself, which I
  checked for all 12 transitions. So the lane's `M_d` and `M_q` recursions are correct.

## (3) Recursions (l. 100–212). Match.

- `M_b(k+1) = M_b·1·M_d·1·M_p·1·1`
- `M_p(k+1) = 1·1·M_b·1·M_q·1·M_p`
- The mirror images give `M_d(k+1)` and `M_q(k+1)`.
- Hence the substitution `b→bdp, d→dbq, p→bqp, q→dpq`, and `f(k+1) = 3f(k)+4`.

## (4) Claim (l. 463–473), Figure `fig:bottom-up-analysis-smart` (l. 475–663), and the passage to Z-tapes

**The figure against the lane's §2 table.**
- For each sub-move type `x ∈ {b,d,p,q}`, the figure lists three parents. The sub-move's two circled cells, which
  are unmodified by it, distinguish them.
- The lane's table matches all twelve parent/index entries.
- It also matches the figure's step numbers:
  - `0`, `f(k)+1` and `2` for `b` and `d` sub-moves;
  - `2f(k)+4`, `2f(k)+2` and `f(k)+3` for `p` and `q` sub-moves.

**Exhaustiveness.** Since `s_+ ∈ {1,2}` and `s_* ∈ {0,1,2}`, the three cases for each `x` are `s_* = 0`,
`(s_* ≠ 0, s_+ = 1)` and `(s_* ≠ 0, s_+ = 2)`. **Correct.**

**Cyclic tapes versus Z.** The source itself licenses local use on infinite configurations (l. 50): "The argument
applies whether or not these are finite subpatterns of a finite cyclic tape, or of an infinite configuration."
- The figure's case analysis uses only the sub-move's domain plus one adjacent cell, with arbitrary content. So on
  `Z` every level-`k` move has a genuine level-`(k+1)` parent, for every `k`.
- The cap at level `ℓ−1` exists only because of wrap-around on cyclic tapes.
- The lane uses the Claim only for locality:
  - The eight level-0 patterns decide `Y`: state, plus a nonzero symbol on the appropriate side.
  - A `b_1` head with a nonzero symbol immediately to its left is level 0. With `0^k` first, it is special of
    level `k`. With `0^∞`, it is "level ∞", which is not in `Y`.
  - Locality needs no cyclic hypothesis. **Correct.**
- **Uniqueness of the canonical chain.** The level-0 move is determined by the state and the side of the nonzero
  neighbour, and each parent is determined by the circled cells (l. 664 onwards). This is what the source proves
  cyclically, and the proof is local.

## (5) Minimality, the 2V encoding, and the first-return lemma

**T1, minimality.**
- `three-v-contains-aperiodic-rationals` quotes Callard–Salo §1: SMART's "moving-tape dynamics is a minimal
  homeomorphism on the Cantor space". It cites COT (J. Comput. System Sci. 84 (2017)), which nobody has read.
- The statement concerns "the SMART machine". Callard–Salo's version duplicates states (Remark l. 39–43).
- Transfer to this version: every move goes from a `·_2` state to a `·_1` state, and every write from `·_1` to
  `·_2`. So `F` alternates the two clopen halves `X_2 → X_1 → X_2`, and `F` is minimal iff `F^2|_{X_2}` is.
  `F^2|_{X_2}` is the one-step machine.
- So minimality transfers, given the source's "completely equivalent" (l. 42). Record this as a trust surface.

**`Y` is clopen and returns are bounded.**
- `Y` is decided by the state and the cells at positions `±1`.
- `F` is minimal, so `⋃_i F^{-i}Y = X`, and compactness gives `C^2 = Y ∪ … ∪ T^{-R}Y` after the
  prefix-code conjugacy.
- This is exactly the hypothesis of `brin-thompson-first-return-maps-lie-in-kv`: `T ∈ kV`, `Y` nonempty clopen,
  finite `R`.
- That node's proof is correct as written. I checked:
  - that the `Y_r` are clopen;
  - bijectivity of `T_Y`;
  - brick-canonicity on `Y_r`;
  - existence of `ψ` by splitting into `s` bricks.
- So `U = ψT_Yψ^{-1} ∈ 2V`. **Hypotheses met.**
- The "at most 4 consecutive special configurations" bound is not used, and I did not check it.

**Counting and factor. Correct.**
- `L(0) = 2` and `L(k+1) = 3L(k)`. The four single steps of a parent create no level-0 configurations, and
  consecutive sub-moves abut with no gap.
- The level-`k` moves in canonical chains are disjoint time intervals.
- Equivariance at a move boundary: `M'` is an interval containing `F_Y y` but not `y`, so `pos_k(F_Y y) = 0`.
- `π` is locally constant at each coordinate, `lim Z/(2·3^k) ≅ Z/2 × Z_3`, and the image is closed and invariant
  under the minimal rotation, so it is onto.
- The route composes this with `ψ^{-1}` and the coding, which gives the map `C^2 → Z_3` that the target hole
  requires.

## N1: novelty

- Callard–Salo contains no odometer, eigenvalue or equicontinuous-factor statement. I grep'd all four source
  files.
- A web search (Salo; Belk–Bleak on 2V; the reversible-TM group papers, arXiv:2303.17270 and 2011.07827) found no
  statement that an element of `2V` factors onto an odometer.
- The Dekking cross-check (a `Z_3` factor for the substitution subshift) is classical but not used.
- Keep "no priority claimed beyond a bounded search".
