# Referee report (gq-referee-c): smart-induced-on-genuine-moves-has-exact-tripling

- **Node:** `research/smart-induced-on-genuine-moves-has-exact-tripling.md` and its `-proof` route, landed
  eddfd3d4b by lane `gq-affq`, with a later indexing correction.
- **Lens:** independent re-derivation from Callard–Salo `prop:smart-moves` and the table.
- **Verdict: PASS** for items 1 and 2, which are the load-bearing ones. Item 3 (checkpoints) is an illustration.
  It agrees with my K = 2 check in
  `gq-referee-c-smart-induced-map-has-brick-local-height-3-renormalization.md` §2.

**Notation.** `▶ = b`, `◀ = d`, `⊳ = p`, `⊲ = q`. `Y` is the set of `b_2`/`d_2` on a nonzero cell, `p_2` with
nonzero right neighbour, and `q_2` with nonzero left neighbour.

## Item 2: exact tripling

**The recursions** are read off the source proof:
- `M_b(k+1) = M_b(k) r M_d(k) r M_p(k) r m`;
- `M_p(k+1) = m r M_b(k) r M_q(k) r M_p(k)`;
- the mirrors for `d` and `q`.

**Step count.** A level-`k` tree has `3^k` leaves and `(3^k − 1)/2` internal nodes. Each internal node adds 3 `r`
steps and 1 `m` step. So the total is `3^k + 4(3^k − 1)/2 = 3^(k+1) − 2 = f(k)`. ✓

**The leaves are in Y.** Every leaf `M_x(0)` has its `s_+ ∈ {1,2}`, because the sub-move boundary values always
have first component `s_+` or a written `1`/`2`. So:
- `b_2`/`d_2` sits on a nonzero cell;
- `p_2`/`q_2` faces a nonzero neighbour.

**The extra `m`'s are not in Y.**
- In `M_b`, the extra `m` is `b_2` on the cell just reset `1 -> 0`.
- In `M_p`, it is `p_2` on `s_*`, whose right neighbour is the first `0`.
- The mirrors behave the same way.

**`r` steps are phase 1**, so never in `Y`. Exactly `3^k` of the steps of `M_x(k)` start in `Y`. ✓

## Item 1: bounded return

The phase-2 configurations outside `Y` are exactly the four listed. Each is traced below, with `t` counting
steps.

- **`b_2` on 0.** At `t = 1` it is `b_1` on the next cell `c`.
  - If `c = 0`: `0|1` gives `d_2` on a `1`, in `Y` at `t = 2`.
  - If `c ≠ 0`: `c|c` gives `q_2` at `t = 2`. Its left neighbour is the original `0`, so it is not in `Y`. At
    `t = 3` it is `q_1` on that `0`. Then `0|2` gives `d_2` on a `2`, in `Y` at `t = 4`.
- **`p_2` whose right neighbour is 0.** At `t = 1` it is `p_1` on the `0`. Then `0|2` gives `b_2` on a `2`, in `Y`
  at `t = 2`.
- **`d_2` and `q_2`** are the mirrors.

A phase-1 configuration reaches phase 2 in one step. So every configuration enters `Y` within 5 steps, and
`r_Y <= 6`. ✓

This is the hypothesis of `brin-thompson-first-return-maps-lie-in-kv` with `R = 5`, which I passed separately.
With the encoding checked in `gq-referee-c-smart-prefix-code-encoding-into-2v.md`, the induced map is conjugate to
an element of `2V`. ✓

## Calibration

- **The additive defect.** Without inducing, `f(k+1) = 3f(k) + 4`. Inducing on `Y` removes exactly the
  `(3^k − 1)/2` extra `m`'s and all the `r` steps. The exact timing `e(k) = 3^k` comes from counting, not from a
  fit.
- **The odometer node** (`smart-level-zero-return-map-factors-onto-3-adic-odometer`) uses a different clopen `Y`,
  with `2·3^k` points per level-`k` move. The height-3 renormalization uses this node's `Y`. I did not re-derive
  the other count here.
