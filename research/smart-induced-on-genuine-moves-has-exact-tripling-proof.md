---
rg: 2
id: smart-induced-on-genuine-moves-has-exact-tripling-proof
kind: route
title: Genuine level-zero moves are exactly the M(0) leaves of the move recursion, and every orbit meets one within five steps
target: smart-induced-on-genuine-moves-has-exact-tripling
requires:
  - brin-thompson-first-return-maps-lie-in-kv
  - three-v-contains-aperiodic-rationals
---

**Table** (Callard–Salo §3, tikz figure; `a|b` reads `a` and writes `b`):
- `▶_2` moves right to `▶_1`. `▶_1`: `0|1` goes to `◀_2`; `1|1` and `2|2` go to `⊲_2`.
- `◀_2` moves left to `◀_1`. `◀_1`: `0|1` goes to `▶_2`; `1|1` and `2|2` go to `⊳_2`.
- `⊳_2` moves right to `⊳_1`. `⊳_1`: `0|2` and `1|0` go to `▶_2`; `2|0` goes to `⊲_2`.
- `⊲_2` moves left to `⊲_1`. `⊲_1`: `0|2` and `1|0` go to `◀_2`; `2|0` goes to `⊳_2`.

**Recursion** (Callard–Salo, Proposition 3.2 and its proof). Write `m` for a phase-2 step and `r`
for a phase-1 step. `M_q(0) = m` is one move. For `k >= 0`:
- `M_▶(k+1) = M_▶(k) r M_◀(k) r M_⊳(k) r m`;
- `M_⊳(k+1) = m r M_▶(k) r M_⊲(k) r M_⊳(k)`;
- `M_◀` and `M_⊲` are the mirror images of these.

Each `M_q(k+1)` therefore contains exactly three sub-moves of level `k`. Its other steps, called
joints, are three `r` steps and one extra `m`. The extra `m` is:
- for `M_▶(k+1)`: `▶_2` on the cell just rewritten from `1` to `0`, moving onto `s_*`;
- for `M_⊳(k+1)`: `⊳_2` on `s_*`, moving onto the first `0` of the block (`k + 1 >= 1` zeros);
- for `M_◀(k+1)` and `M_⊲(k+1)`: the mirror images.

**Item 2.** By induction on `k`, the phase-2 steps of `M_q(k)` are of two kinds:
- the leaves `M_{q'}(0)` of the recursion tree, of which there are exactly `3^k`;
- extra `m`'s of the internal nodes.

Every leaf `M_{q'}(0)` is applied to its pattern in Proposition 3.2, so it lies in `Y`:
- `M_▶(0)` and `M_◀(0)` have the head on `s_+ ≠ 0`;
- `M_⊳(0)` and `M_⊲(0)` move onto `s_+ ≠ 0`.

Every extra `m` lies outside `Y`: the head is on a `0`, or moves onto a `0`, as listed above.
So exactly `3^k` steps of `M_q(k)` start in `Y`. ∎

*Check at `k = 1`* for `▶_2` on `s_+ 0 s_*`, step by step (Y marks a step starting in `Y`):
1. `m`, Y.
2. `r`: `0|1`.
3. `m`, Y: `◀_2` on the new `1`.
4. `r`: `s_+|s_+`.
5. `m`, Y: `⊳_2` on `s_+` with right neighbour `1`.
6. `r`: `1|0`.
7. `m`, not in Y: `▶_2` on `0`.

That is 7 steps, 3 of them in `Y`, and the tape is restored.

**Item 1.** Phase-1 configurations become phase 2 in one step. The phase-2 configurations outside
`Y` are:
- `▶_2` on `0`. It moves onto a cell `c`.
  - If `c = 0`: `0|1` gives `◀_2` on a `1`, which is in `Y` after 2 steps.
  - If `c ≠ 0`: `c|c` gives `⊲_2` whose left neighbour is the `0`. That moves left, `0|2` gives
    `◀_2` on a `2`, which is in `Y` after 4 steps.
- `◀_2` on `0`: the mirror case, at most 4 steps.
- `⊳_2` with right neighbour `0`. It moves right, `0|2` gives `▶_2` on a `2`, which is in `Y`
  after 2 steps.
- `⊲_2` with left neighbour `0`: the mirror case, 2 steps.

So every configuration enters `Y` within `1 + 4 = 5` steps, and `r_Y <= 6`.
- `Y` is clopen, since membership reads the state and at most two cells.
- `F` is the moving-tape map of a reversible Turing machine, so `F ∈ 2V` by the prefix-code
  conjugacy of item 1 of `three-v-contains-aperiodic-rationals-proof`. That proof is written for
  any finite state set: use a complete prefix code with 8 words for `Q`.
- `brin-thompson-first-return-maps-lie-in-kv` then gives a brick-local `ψ` with
  `S = ψ F_Y ψ^{-1} ∈ 2V`. ∎

**Item 3**, by the step lists above. Times count `F`-steps from `y_{k+1}`.
- *Fine run.* The steps in `Y` are at times 0, 2, 4, 8, 10, 12, 18, … These are
  `S^0, …, S^6`:
  - time 8 (`S^3`) is `◀_2` on cell 2, which holds the `1` written at time 7;
  - time 18 (`S^6`) is `▶_2` on cell 1, which holds the `2` written at time 17 (by `⊳_1`, `0|2`), with
    cell 2 equal to `1`. On the way: at time 13, `⊲_1` rewrites cell 1 from `1` to `0`; at time 14 an
    extra `m` takes the head onto `s_+`; at time 15 `◀_1` reads `s_+`; at time 16 an extra `m` moves
    it back to cell 1.
- *Coarse run from `y_k`.* The steps in `Y` are at times 0, 2, 4, 8, …:
  - time 2 is `◀_2` on cell 1, which holds a `1`;
  - time 4 is `⊳_2` on `s_+`.

Comparing time 8 of the fine run with time 2 of the coarse run, and time 18 with time 4, gives
the two checkpoints stated in item 3. An earlier landing (eddfd3d4b) compared time 12, which is
`S^5`, with time 4; that was an indexing error, corrected here. ∎
