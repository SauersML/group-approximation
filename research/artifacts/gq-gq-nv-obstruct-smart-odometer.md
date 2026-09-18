# SMART, induced on its level-0 configurations, factors onto the 3-adic odometer (lane gq-nv-obstruct, 2026-09-17)

Status: proof claimed, under review by gq-referee-a and gq-referee-b. Target hole:
`some-brin-thompson-element-factors-onto-an-odometer`. Answer claimed: YES, with `k = 2` and `m = 3`.

Source: Callard–Salo, arXiv:2208.00685v3, e-print file `distortion-1-smart.tex` (read locally at
`$GQ/src/callard-salo/`): the transition table (l. 2–35), Proposition `prop:smart-moves` (l. 52–214), and
the level-0 trichotomy Claim and Figure `fig:bottom-up-analysis-smart` (l. 390–664).

## 1. Inputs, verbatim

- **Machine.** `Q = {b_1,d_1,p_1,q_1} ∪ {b_2,d_2,p_2,q_2}`, `Γ = {0,1,2}`, in the Kari–Ollinger model:
  transitions are either moves `(q,±1,q')` or symbol transitions `(q,a,q',b)`. `b, d` are filled; `p, q` are
  hollow.
  - Moves: `b_2 ▶ b_1`, `d_2 ◀ d_1`, `p_2 ▶ p_1`, `q_2 ◀ q_1`.
  - Symbols: `b_1: 0|1 → d_2`, `1|1, 2|2 → q_2`; `d_1: 0|1 → b_2`, `1|1, 2|2 → p_2`;
    `p_1: 0|2, 1|0 → b_2`, `2|0 → q_2`; `q_1: 0|2, 1|0 → d_2`, `2|0 → p_2`.
- **Prop. `prop:smart-moves`.** "Let f(k) = 3^{k+1}−2. For all k, s_* ∈ {0,1,2} and s_+ ∈ {1,2}", the moves
  hold. For example, `M_b(k)` takes `(s_+ 0^k s_*)` with `b_2` on `s_+` to the same tape with `b_1` on
  `s_*`, in `f(k)` steps, and similarly for `M_d`, `M_p`, `M_q`. "Additionally, the cell containing s_* is
  only visited at the last (resp. first) step of the sequences of transitions M_b and M_d (resp. M_p and
  M_q). And the cell containing s_+ is never modified."
- **Recursion** (from its proof, l. 100–212; `d, q` by the stated `b↔d`, `p↔q` mirror symmetry):
  - `M_b(k+1) = M_b(k) · 1 · M_d(k) · 1 · M_p(k) · 1 · 1`
  - `M_p(k+1) = 1 · 1 · M_b(k) · 1 · M_q(k) · 1 · M_p(k)`
  - mirrored: `M_d(k+1) = M_d(k) · 1 · M_b(k) · 1 · M_q(k) · 1 · 1` and
    `M_q(k+1) = 1 · 1 · M_d(k) · 1 · M_p(k) · 1 · M_q(k)`

  I re-checked every transition of the `b` and `p` recursions against the table above. So the sub-move
  sequences are **b → (b,d,p), d → (d,b,q), p → (b,q,p), q → (d,p,q)**: a substitution of constant length 3.
- **Claim (l. 463–473).** A configuration with a head either performs a step of a level-0 move
  `M_x(0)` (eight local patterns), or contains a special pattern of level `k >= 1` (the first two
  configurations of a `p/q` move, or the last two of a `b/d` move). On cyclic tapes the remaining case is
  the shift of an initial configuration; on `Z` the remaining case is level `∞`. "The level is determined
  by the distance to the nearest nonzero symbol in an appropriate direction." So all cases are local.
- **Figure `fig:bottom-up-analysis-smart` (l. 475–663).** A level-`k` computation lies in a level-`(k+1)`
  computation, which is "uniquely determined by considering the value of two cells (circled on the figure)
  which are left unmodified by the computation of level k". These are the sub-move's own `s_+` and `s_*`
  cells. The step index in the parent is determined as well.

## 2. The case analysis on Z

For a sub-move of type `x` at level `k`, write `s_+`, `s_*` for its two end cells. By Prop. `prop:smart-moves`,
neither is changed during the sub-move. The figure's cases, which I re-derived from the recursions:

| sub-move | `s_* = 0` | `s_* ≠ 0`, `s_+ = 1` | `s_* ≠ 0`, `s_+ = 2` |
|---|---|---|---|
| `M_b(k)` | in `M_b(k+1)`, index 0 | in `M_d(k+1)`, index 1 | in `M_p(k+1)`, index 0 |
| `M_d(k)` | in `M_d(k+1)`, index 0 | in `M_b(k+1)`, index 1 | in `M_q(k+1)`, index 0 |
| `M_p(k)` | in `M_p(k+1)`, index 2 | in `M_b(k+1)`, index 2 | in `M_q(k+1)`, index 1 |
| `M_q(k)` | in `M_q(k+1)`, index 2 | in `M_d(k+1)`, index 2 | in `M_p(k+1)`, index 1 |

- **The parent is genuine.** The parent's domain is the sub-move's domain extended by one cell, whose
  content is arbitrary (the parent's `s_*`). The current configuration therefore equals the parent's
  pattern at the corresponding step.
- **It runs as described.** By determinism and reversibility, the actual orbit runs that parent move
  forward to its end and backward to its start. The parent never leaves its domain, by the proposition.
- The table is exhaustive, because `s_+ ∈ {1,2}` and `s_* ∈ {0,1,2}`. So on `Z`, **every level-0
  configuration lies in a canonical chain of genuine moves of every level `k`**.
- Level-`k` moves in this chain have domains of `k + 2` cells containing the head.

## 3. The induced map and its odometer factor

- **The return set.** Let `X = Γ^Z × Q` be the moving-tape space and `F` the SMART homeomorphism. Let
  `Y ⊂ X` be the set of level-0 configurations. It is clopen, since it is decided by the state and the
  cells at positions `0, ±1`.
- **Bounded returns.** `F` is minimal (Callard–Salo §1, verbatim in `three-v-contains-aperiodic-rationals`),
  so the open cover `{F^-i Y}` of `X` has a finite subcover. So `F` returns to `Y` within a bounded time. A
  direct count from the recursions gives at most 4 consecutive special configurations.
- **Counting.** Let `L(k)` be the number of level-0 configurations in a level-`k` move. `L(0) = 2`, since
  `M_x(0)` is one transition with two configurations. `L(k+1) = 3 L(k)`, since the special configurations
  are not level-0. So `L(k) = 2·3^k`.
  - In the time of the induced map `F_Y`, the three sub-moves of a move occupy consecutive blocks of
    length `L(k)`.
  - Distinct canonical level-`k` moves are disjoint time intervals: two genuine moves sharing a
    configuration share its canonical chain.
- **The position function.** For `y ∈ Y`, let `pos_k(y) ∈ [0, 2·3^k)` be the number of level-0
  configurations of its level-`k` move that come before `y`. Then `pos_0 = j_0 ∈ {0,1}`, the step within
  `M_x(0)`, and `pos_{k+1} = i_k · 2·3^k + pos_k`, where `i_k` is the index from the table.
  - So `pos_k` is locally constant: it depends only on the `k+2` cells of the level-`k` domain around the
    head.
  - `pos_{k+1} ≡ pos_k mod 2·3^k`.
- **Equivariance.** `pos_k(F_Y y) ≡ pos_k(y) + 1 mod 2·3^k`.
  - Inside a move, `pos_k` increases by 1.
  - If `y` is the last level-0 configuration of its level-`k` move `M`, then `F_Y y` lies in a different
    move `M'`. `M'` is a time interval that contains `F_Y y` but not `y`, so it lies entirely after `y`.
    Only special configurations lie between `y` and `F_Y y`. So `pos_k(F_Y y) = 0`.
- **The factor.** `π = (pos_k)_k : Y → lim Z/(2·3^k) ≅ Z/2 × Z_3` is continuous and satisfies
  `π ∘ F_Y = π + 1`. Its image is closed, nonempty and invariant under the minimal rotation `+1`, so `π`
  is onto. Composing with the projection to `Z_3` gives the 3-adic odometer factor.
- **Into 2V.** `F` is conjugate through complete prefix codes to an element `T ∈ 2V`
  (`three-v-contains-aperiodic-rationals`, item 1). The set `Y` maps to a clopen set with bounded returns.
  By `brin-thompson-first-return-maps-lie-in-kv`, `U = ψ T_Y ψ^-1 ∈ 2V` for a brick-local `ψ`, and
  `π ∘ (coding)^-1 ∘ ψ^-1 : C^2 → Z_3` is the required factor map.

## 4. Remarks

- **SMART itself.** `F` probably has no 3-adic eigenvalues. Relative to its parent's start, a level-`k`
  sub-move starts at time `i·3^{k+1} + ε`, with `ε ∈ {0,−1,−2}` (in `b/d` parents) or `{2,1,0}` (in `p/q`
  parents). The small `ε` of every ancestor survives modulo `3^{k+1}`. Inducing on `Y` removes exactly
  these offsets. This point is not proved and not needed.
- **Dekking cross-check.** The sub-move sequences form the primitive constant-length-3 substitution
  `b→bdp, d→dbq, p→bqp, q→dpq`. Primitivity: `σ^2(b)` contains all letters. Dekking's theorem gives a `Z_3`
  factor of its subshift. The argument above does not use this.
- **Not claimed.** A height-3 renormalization `(A, φ)` of `U` with brick-local `φ`. That is what
  `renormalizable-thompson-elements-give-baumslag-solitar` needs for `BS(1,3) <= 3V`. The level-`k` to
  level-`(k+1)` recodings of Callard–Salo have pattern lengths growing with `k`, so they are not one
  brick-local `φ`.

## 5. Revisions after review (2026-09-18)

Both referees passed the proof. Changes, all reflected in
`smart-level-zero-return-map-factors-onto-3-adic-odometer-proof`:
- **Bounded returns, proved directly.** In a finite chain at most 4 specials are consecutive, since no
  `b/d` move is a last sub-move and no `p/q` move is a first sub-move. Every configuration of infinite level
  enters `Y` within 5 steps (all eight cases checked). So every return time is at most 10, and SMART's
  minimality is no longer needed.
- **Coding into 2V** uses the 8-state machine with a size-24 complete prefix code for (state, head cell).
  The 4-state coding of `three-v-contains-aperiodic-rationals` is not used.
- **Radius.** `pos_k` depends on the cells within distance `k+1` of the head.
- The "at most 4" count in §3 is now proved, as above.
