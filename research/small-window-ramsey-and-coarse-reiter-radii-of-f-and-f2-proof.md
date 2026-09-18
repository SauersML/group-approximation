---
rg: 2
id: small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2-proof
kind: route
title: Dualize both radii by the finite minimax theorem, bound the free group by a forest count and coarea, and settle the small radii of F and F_2 by LPs whose primal and dual optima are rationalized and rechecked in exact arithmetic
target: small-window-ramsey-and-coarse-reiter-radii-of-f-and-f2
requires: [moore-ramsey-criterion-for-amenability, thompson-f-b1-ramsey-witnesses-are-at-most-one-third]
artifacts:
  - experiments/window-two-ramsey-calibration-2026-09-17/window2.py
  - experiments/window-two-ramsey-calibration-2026-09-17/alternate.py
  - experiments/window-two-ramsey-calibration-2026-09-17/verify_witnesses.py
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_lp.py
  - experiments/window-two-ramsey-calibration-2026-09-17/free_F2_B2.json
  - experiments/window-two-ramsey-calibration-2026-09-17/thompson_F_B2_n4-8.json
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_F2_r1-5.json
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_F_r3-8.json
  - experiments/window-two-ramsey-calibration-2026-09-17/cr_F_M2_r4-6.log
  - experiments/window-two-ramsey-calibration-2026-09-17/alternate_F_B2_n7-8.json
  - experiments/window-two-ramsey-calibration-2026-09-17/verify_alternate_F_B2_n7-8.jsonl
  - experiments/window-two-ramsey-calibration-2026-09-17/alternate_F_B2_n7-9_search.log
---

Notation is as in the claim. All sets and measures are finite, `P(X)` is the simplex of probability vectors on
`X`, and `μν(E) = Σ_{xy∈E} μ(x)ν(y)` is Moore's convolution (quoted in `moore-ramsey-criterion-for-amenability`).

**Step 1 (Ramsey dual, item 1).** Fix `m ≤ n` and `E ⊆ B_n`.
- The condition `P(B_m)ν ⊆ P(B_n)` says `B_m · supp ν ⊆ B_n`, that is `supp ν ⊆ I_n`.
- `μ ↦ μν(E)` is affine, so `|μν(E) − μ'ν(E)| ≤ 1/2` for all `μ, μ'` iff it holds for point masses `δ_a, δ_b`.
  Now `δ_aν(E) = Σ_x ν(x) 1_E(ax)`.
- So `E` defeats `B_n` iff `min_{ν∈P(I_n)} max_{(a,b)} Φ(ν, a, b) > 1/2`, where
  `Φ(ν, a, b) = Σ_x ν(x)(1_E(ax) − 1_E(bx))`.
- `Φ` is bilinear in `ν` and in a mixed strategy `λ ∈ P(B_m × B_m)`, and both simplices are finite. Von Neumann's
  minimax theorem gives `min_ν max_λ = max_λ min_ν`. The inner minimum of a linear function over `P(I_n)` is attained
  at a point mass. So `E` defeats `B_n` iff some `λ` has `Σ λ(a,b)(1_E(ax) − 1_E(bx)) > 1/2` for every `x ∈ I_n`.
  If `I_n = ∅`, both sides hold vacuously.
- `B_n` is not 1/2-Ramsey for `B_m` iff some `E ⊆ B_n` defeats it. By monotonicity in `B` (criterion node),
  this happens for every `n' ≤ n` as well. So `R(m) > n`.
- The row indexed by `x` is `(χ_{X_E(x)}(a) − χ_{X_E(x)}(b))_{(a,b)}`, so it depends only on the picture `X_E(x)`.

**Step 2 (coarse Reiter dual, item 2).** Fix `ν ∈ P(B_r)` and `g ∈ B_M`.
- `gν` and `ν` have equal mass, so `‖gν − ν‖₁ = 2 max_D (gν(D) − ν(D))`. Here `D` ranges over subsets of
  `B_{r+M}` without loss, and `gν(D) = ν(g^{-1}D) = Σ_x ν(x) 1_D(gx)`.
- Hence `CR(M) > r` iff every `ν ∈ P(B_r)` has some `(g, D)` with `Σ_x ν(x)(1_D(gx) − 1_D(x)) > 1/2`.
- The pure strategies `(g, D)` form a finite set. The same minimax step turns this into a probability `μ` on
  pairs `(g, D)` with `Σ μ(g,D)(1_D(gx) − 1_D(x)) > 1/2` for every `x ∈ B_r`.

**Step 3 (translate coherence, item 3).** Take a Ramsey certificate `(E, λ)` at `(m, n)`. Push `λ` forward under
`(a, b) ↦ (g, D) = (b^{-1}a, b^{-1}E)`. Then `1_D(gx) = 1_E(ax)` and `1_D(x) = 1_E(bx)`, so the row at `x` is unchanged.
`g ∈ B_{2m}` and `I_n ⊇ B_{n−m}`. So the push-forward is a coarse certificate for `(2m, n−m)`, and
`CR(2m) > n − m`. With `n = R(m) − 1` this is `R(m) ≤ CR(2m) + m`. For the converse, suppose every pair in the
support of `μ` has the form `(b^{-1}a, b^{-1}E)` with `a, b ∈ B_m`, and suppose `μ` is valid on a set containing
`I_n`. Pulling back gives a Ramsey certificate at `(m, n)`.

**Step 4 (free group, coarse side, item 4).** The left Cayley graph of `F_2` (edges `x — sx`) is the 4-regular tree.
Let `A` be finite and nonempty, and let its induced subgraph have `c ≥ 1` components.
- That subgraph is a forest with `|A| − c` edges. Counting degrees, `4|A| = 2(|A| − c) + |∂A|`, where `∂A` is the set
  of pairs `(x, s)` with `x ∈ A` and `sx ∉ A`. So `|∂A| = 2|A| + 2c ≥ 2|A| + 2`.
- `|∂A| = Σ_s |sA \ A|` and `|sA △ A| = 2|sA \ A|`, so `Σ_{s∈S^{±1}} |sA △ A| ≥ 4|A| + 4`.
- For `ν ∈ P(F_2)` with finite support, put `A_t = {ν > t}`. Then `{sν > t} = sA_t`. The layer-cake identity
  `|p − q| = ∫_0^∞ |1[p>t] − 1[q>t]| dt` for `p, q ≥ 0` gives `‖sν − ν‖₁ = ∫_0^∞ |sA_t △ A_t| dt`.
- Hence `Σ_s ‖sν − ν‖₁ ≥ ∫_0^{max ν} (4|A_t| + 4) dt = 4 + 4 max ν`, so `max_s ‖sν − ν‖₁ ≥ 1 + max ν > 1`.
  So no finitely supported `ν` is coarsely `B_1`-invariant, and `CR_{F_2}(1) = ∞`.
- For `ν` uniform on `B_r`, `max ν = 1/|B_r|` is the smallest possible value on `B_r`. Also
  `‖sν − ν‖ = 2|sB_r \ B_r|/|B_r| = 2·3^r/(2·3^r − 1) = 1 + 1/|B_r|`. So `v_{F_2}(r) = 1 + 1/|B_r|` exactly.
  The LP output `cr_F2_r1-5.json` reproduces this for `r ≤ 5`.

**Step 5 (free group, Ramsey side, item 5).** Let `E` be the set of reduced words whose first letter is `b^{±1}`.
- For `|α| ≤ 2` and a reduced word `x` with `|x| ≥ 3`, at most two letters cancel in `αx`. The first letter of `αx`
  is therefore determined by `α` and the length-3 prefix of `x`. So every row of the Step 1 dual that occurs anywhere
  in `F_2` already occurs for some `x` with `|x| ≤ 3`.
- `window2.py free` enumerates those rows. There are 18 distinct pictures. It solves the LP and rationalizes `λ`,
  then recomputes the minimum in `Fraction`s: `5/6`.
- The optimal `λ` is uniform on six pairs:
  `(ba, ab^{-1}), (ba^{-1}, ab), (b², a²), (b^{-1}a, a^{-2}), (b^{-1}a^{-1}, a^{-1}b), (b^{-2}, a^{-1}b^{-1})`.
- For `x ∈ I_n` we have `B_2 x ⊆ B_n`, so `1_{E∩B_n}(αx) = 1_E(αx)`. Hence `(E ∩ B_n, λ)` is a certificate of
  value `5/6 > 1/2` at `(2, n)` for every `n`, and `R_{F_2}(2) = ∞`. `R_{F_2}(1) = 3` is imported from
  `thompson-f-b1-ramsey-witnesses-are-at-most-one-third`.

**Step 6 (Thompson's F, coarse side, item 6).** Let `v_M(r) = min_{ν∈P(B_r)} max_{g∈B_M∖{e}} ‖gν − ν‖₁`.
`P(B_r) ⊆ P(B_{r+1})`, so `v_M` is nonincreasing and `CR(M) = min{r : v_M(r) ≤ 1}`. `cr_lp.py` certifies
both bounds in `Fraction` arithmetic.
- Upper bound: `cr_lp.py` rationalizes the primal LP solution to a probability `ν` on `B_r`, then recomputes
  `max_g Σ_y |ν(g^{-1}y) − ν(y)|` exactly.
- Lower bound: `cr_lp.py` rationalizes a dual `(w, c)`, then renormalizes `w` to a probability on `B_M∖{e}`
  and clips `c` so that `|c_{g,y}| ≤ w_g`. For every `ν` on `B_r`:
  `max_g ‖gν − ν‖ ≥ Σ_g w_g ‖gν − ν‖ ≥ Σ_g Σ_y c_{g,y}(gν(y) − ν(y)) = Σ_x ν(x) h(x)`,
  where `h(x) = Σ_g (c_{g,gx} − c_{g,x})`. So `v_M(r) ≥ min_{x∈B_r} h(x)`. This needs `c_{g,·}` only on
  `B_r ∪ gB_r`, which is where it is defined.
- `M = 1` (`cr_F_r3-8.json`): the lower and upper bounds coincide.

  | r | 3 | 4 | 5 | 6 | 7 | 8 |
  |---|---|---|---|---|---|---|
  | `v_1(r)` | 54/53 | 162/161 | 56/65 | 102/125 | 92/119 | 334/449 |
  | `\|B_r\|` | 53 | 161 | 475 | 1381 | 3957 | 11237 |

  So `v_1(4) > 1 ≥ v_1(5)` and `CR_F(1) = 5`.
- For `r ≤ 4` the computed values are `v_1(r) = 1 + 1/|B_r|`, the free value of Step 4, and the computed ball
  sizes `1, 5, 17, 53, 161` are the free ones. At `r = 5`, `|B_5(F)| = 475 < 485 = |B_5(F_2)|`, and the value
  drops below 1 at once, with an optimal `ν` of support 65. This is the radius at which `F`'s ball stops looking
  free. These remarks are commentary: the exact values in the table are the whole proof of item 6.
- `M = 2` (`cr_F_M2_r4-6.log`, the stderr of `cr_lp.py F 4 7 2` stopped during `r = 7`, one JSON record per
  finished radius; `w` ranges over the 16 elements of `B_2 ∖ {e}`): the lower and upper bounds coincide at `v_2(4) = 3134/2387`,
  `v_2(5) = 5441/4299` and `v_2(6) = 2207/1795`, all `> 1`. So `CR_F(2) ≥ 7`.

**Step 7 (Thompson's F, Ramsey side, item 7).** `R_F(1) = 3` is imported from
`thompson-f-b1-ramsey-witnesses-are-at-most-one-third`. For window 2 we use Step 1 at `(m, n) = (2, 7)` and
`(2, 8)`.
- `alternate.py 7 8 5 400` produced the pairs `(E, λ)` recorded in `alternate_F_B2_n7-8.json`, as follows.
  - Start from the transplanted cone `E = {g : some geodesic of g begins with x_1^{±1}}`.
  - Alternate an LP for `λ` given `E` with a MILP for `E ⊆ B_n` given `λ`.
  - Keep the best pair whose value, rationalized, is `> 1/2`.
- Each record lists:
  - the 17 words of length `≤ 2` spanning `B_2`;
  - `λ` as fractions;
  - `E` as a list of geodesic words.
- `verify_witnesses.py`, run on `alternate_F_B2_n7-8.json` (output `verify_alternate_F_B2_n7-8.jsonl`), shares
  only the group law `f_mul` and the BFS `ball` with the search code. It does the following.
  - Rebuilds `B_n` by BFS.
  - Rebuilds every element of `E` from its word, and checks that the word is geodesic and lies in `B_n`.
  - Checks that `λ` is a probability with positive entries.
  - Recomputes `I_n = {x ∈ B_n : Wx ⊆ B_n}` for the listed window `W`.
  - Evaluates `min_{x∈I_n} Σ λ(a,b)(1_E(ax) − 1_E(bx))` in `Fraction`s.
- Results:

  | n | `\|I_n\|` | `\|E\|` | exact minimum |
  |---|---|---|---|
  | 7 | 475 | 1156 | 3/5 |
  | 8 | 1381 | 4916 | 7/12 |

- The listed words have length `≤ 2`, so `W ⊆ B_2`. Hence `λ` is a probability on `B_2 × B_2`, and
  `I_n(B_2) ⊆ I_n(W)`. So the check covers every row that Step 1 requires. Both minima exceed `1/2`, so
  `R_F(2) > 8`.
- The 17 words are in fact distinct elements, so `W = B_2`. This is not needed for the bound.
- Context, not used in the proof:
  - For the untouched transplanted cones (`thompson_F_B2_n4-8.json`), the LP value for the best `λ` is
    `7/8, 10/13, 7/10` at `n = 4, 5, 6`, and it falls to `1/2` at `n = 7`. So the free witness of Step 5 does
    not survive transplantation past radius 6. The MILP is needed from `n = 7` on.
  - The same alternation at `n = 9` (`alternate_F_B2_n7-9_search.log`) stalled at `29/60`. That is a search
    outcome and bounds nothing.
