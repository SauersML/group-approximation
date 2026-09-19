---
rg: 2
id: thompson-f-tower-size-laws-have-zero-defect
kind: claim
title: A left-dominant iterated-exponential tower law on N leaves makes the law of (offset plus interval sum of sizes, offset plus interval max of depths) the same, up to any epsilon, for every cut of the leaves into w+1 consecutive intervals; so separated relative scales in a randomly placed cluster, not overlapping windows, are what zero defect of Guba-set piece sizes needs at width at least 4
distinct_from:
  thompson-f-tree-size-observations-have-zero-defect: that is the shadow-defect statement for the observation Sigma_K of prefix sizes, depths and exact tail on the Guba sets; this is an abstract probabilistic lemma about interval sums of one tower law on N ordered leaves, with no forests, words or defect in it. The route thompson-f-tree-size-observations-via-tower-law derives that node from this one plus Lemma 1 there.
  thompson-f-hierarchical-size-laws-die-at-width-four: that kills laws whose middle sizes sit in finitely many levels separated by deterministic thresholds, with tight weights inside a level; the tower law has every ratio of distinct leaf sizes separated but its scale cluster sits at a uniformly random height, so no deterministic threshold separates it, and it lies outside that class. It refutes the survivor description there ("some ratio neither tight nor separated"), not its theorem.
  thompson-f-dyadic-ea-witnesses-need-tower-size: that is about the size of dyadic elementary-amenable witnesses; tower there means the height of an exponential bound on witness size, here it is the structure of a probability law on leaf sizes.
  thompson-f-exact-tail-observations-have-zero-defect: that couples forests by a tower coupling through an idempotent probability of a prefix invariant; the tower here is an iterated exponential scale law for integers, and sizes carry no idempotent measure.
artifacts:
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.py
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.out
  - experiments/thompson-f-relative-levels-2026-09-17/order_colgen.py
  - experiments/thompson-f-relative-levels-2026-09-17/order_colgen_0_4.out
  - experiments/thompson-f-relative-levels-2026-09-17/relative_level_lp.py
  - experiments/thompson-f-relative-levels-2026-09-17/relative_colgen.py
  - experiments/thompson-f-relative-levels-2026-09-17/relative_rules.py
  - experiments/thompson-f-relative-levels-2026-09-17/relative_sat.py
  - experiments/thompson-f-relative-levels-2026-09-17/relative_scouting_0_4.out
---

**ESTABLISHED** (agent-verified; complete proof in `thompson-f-tower-size-laws-have-zero-defect-proof`).

## Statement

Fix integers `N >= 1`, `w >= 0`, `c >= 0`. A **cut** is a sequence `1 = a_0 < a_1 < ... < a_w <= N`. Its
intervals are `I_j = [a_j, a_(j+1) − 1]` for `j < w` and `I_w = [a_w, N]`. They are consecutive and cover
`1..N`. An **offset** is a pair `b, f ∈ {0, ..., c}^(w+1)`.

**Theorem (tower lemma).** For every `ε > 0` there is a finitely supported law of positive integers
`(n_v, e_v)_(v = 1..N)` with the following two properties.

1. **Realizable.** Almost surely `⌈log2(n_v + 1)⌉ <= e_v <= n_v` for every `v`. So there is a binary tree
   `X_v` with `n_v` carets and depth `e_v`.
2. **Cut-blind.** For every two cuts `a, a'` and every two offsets `(b, f), (b', f')`, the laws of the
   vectors
   `Y(a, b, f) = ( b_j + Σ_(v ∈ I_j) n_v ,  f_j + max_(v ∈ I_j) e_v )_(j = 0..w)`
   and `Y(a', b', f')` are at total variation distance at most `ε`.

The law is explicit (below). The sizes `n` and the depths `e` are independent towers of the same kind.

## The tower law

**One stage.** It has parameters `R_0, R, G >= 1` and a random vector `g = (g_v)_(v = 1..N−1)` with
`g_v >= G`, independent of everything else in the stage.
- `λ` is uniform on `{R_0, ..., R_0 + R}`.
- `D_v = Σ_(v <= i <= N−1) g_i`, so `D_N = 0` and `D_v − D_(v+1) = g_v >= G`.
- Given `(λ, g)`, the `u_v` are independent and uniform on `{0, ..., 2^(λ + D_v) − 1}`.
- `n_v = 2^(λ + D_v) + u_v`. So `n_v ∈ [2^(λ+D_v), 2^(λ+D_v+1))`.

The leaf sizes are therefore **left-dominant**: `n_v > 2^(G−1) n_(v+1)`. The leftmost leaf of an interval
carries all of its sum up to a factor `1 + O(N 2^(1−G))`, and it is strictly the largest.

**The tower.** Stage `t = 1, ..., w + 1` lives on `N − t + 1` leaves. The gaps of stage `t <= w` are
`g^(t)_v = G_t + n^(t+1)_v`, where `n^(t+1)` is stage `t + 1`, drawn independently. The last stage has
constant gaps `g^(w+1)_v = G_(w+1)`. The sizes are `n = n^(1)`. The depths `e` are an independent copy of
the same construction with their own parameters.

**Parameter order** (this is where `ε` enters).
1. Take every `G_t` large.
2. Take every `R_0^(t)` with `2^(R_0^(t)) >= c_t / ε`, where `c_1 = c` and `c_t = G_(t−1) N` for `t >= 2`.
3. Choose the `R^(t)` bottom-up, from `t = w + 1` to `t = 1`, with `R^(t) + 1 >= E[D^(t)_1] / ε`. This is
   possible because `D^(t)_1` is a bounded function of stage `t + 1` only.
4. For realizability, put `C_e = R^e + max D^e_1 + 1` and `C_n = R + max D_1 + 1` (top stages of the
   depth and size towers). Both are fixed by steps 1 to 3. Raise `R_0^e` until
   `2^(R_0^e) >= R_0^e + C_e + C_n`, and set the top size `R_0 = R_0^e + C_e`. Then
   - `e_v >= 2^(R_0^e) >= R_0 + R + D_1 + 1 >= ⌈log2(n_v + 1)⌉`, and
   - `e_v < 2^(R_0^e + C_e) = 2^(R_0) <= n_v`.

   Raising a top `R_0` only lowers the error bounds, so there is no circularity.

## Why it is cut-blind (the idea; full proof in the route)

For a cut `a`, the size coordinates are `n_(a_j) + E_j`, where the garbage `E_j` is at most
`c + Σ_(v ∈ I_j, v > a_j) n_v`. That is negligible against the scale `2^(λ + D_(a_j))` of the dominant
uniform. So, up to `O(c 2^(−R_0) + N 2^(1−G))` per coordinate, the size vector is a fixed kernel applied
to the **log-scale vector** `x_j = λ + D_(a_j)`.

That vector is in bijection with `(x_w, F_0, ..., F_(w−1))`, where `F_i = D_(a_i) − D_(a_(i+1))` is the sum
of `g` over `I_i`. The uniform `λ` on a window much longer than `D_1` absorbs the one coordinate `x_w`. The
remaining gap vector is `F_i = G_1 |I_i| + Σ_(v ∈ I_i) n^(2)_v`, which is an instance of the same problem:
- one stage lower;
- one coordinate fewer;
- offsets at most `G_1 N`.

After `w + 1` stages nothing is left, and the law no longer depends on the cut. The depth coordinates are
`f_j + e_(a_j)`, because left-dominance makes the maximum over `I_j` equal to its first entry. So they are
handled by the same lemma with constant garbage. The two towers are independent, so the total variation
distances add.

## Consequence for Thompson's F

Route `thompson-f-tree-size-observations-via-tower-law` applies the theorem to the Guba sets:
- put complete depth-`d` tops on roots `0..m`;
- hang `X_v` at the `N = (m + 1) 2^d` depth-`d` leaves;
- keep the tail trivial.

The pieces of `split_s z` are then subtrees over consecutive leaf intervals. Their sizes and depths have
exactly the offset form above, with `c = 2^d` (checked for 13 values of `(m, d)` up to width 5 by
`tower_check.py`). So `δ_1(Σ_K) = 0` for **every** `S_(m+1,m+d+1)`, which is the boxed statement of
`thompson-f-tree-size-observations-have-zero-defect` at all widths.

## Where it sits relative to the earlier kills

- **Class `P`** (Theorem 2 of the size node) has one common scale and fixed weights. The tower has `N`
  scales whose relative gaps are themselves random.
- **Class `H`** (`thompson-f-hierarchical-size-laws-die-at-width-four`) has finitely many levels in
  deterministic windows `θ_ℓ << Λ_ℓ << θ_(ℓ+1)`, with tight weights. In the tower all `N` leaf scales lie
  in a cluster of log-width `D_1`, and that cluster sits at a uniform height `λ` in a window of length
  `R >> D_1`. For any `L` fixed thresholds, with probability at least `1 − L D_1 / R` no threshold meets the
  cluster. All leaves would then share one level, and their ratios, of order at least `2^(G−1)`, violate
  tightness (H1). So the tower is not in `H`, and the theorem of that node is untouched.
- **Correction.** That node's title and its "What survives" section say that every zero-defect law at
  width `>= 4` must have "some middle size ratio that is neither tight nor separated (overlapping scale
  windows)". This is **false**. In the tower law every ratio of distinct leaf sizes tends to `0` or `∞`.
  What the kill of `H` actually forces is weaker: the separation cannot be realized by deterministic
  absolute windows. Relatively separated scales at a random common height survive, and they are exactly
  the mechanism here.
- **Why a few relative levels are not enough (scouting, numerics only).** The model of
  `relative_level_lp.py` has integer levels `1..L` on the middle leaves, a common random scale, and one
  random level ratio. Its observation keeps only the ordered level partition, the weights inside a
  block and the level-gap ratios. At `(0,4)`, `relative_scouting_0_4.out` shows:
  - no level function in `{1..L}^14` with `L = 2, 3` survives the pointwise monotone-pair rules
    (`relative_rules.py`);
  - the exact LP optimum for `L = 2` is `10.234 > 0` (`relative_colgen.py`).

  The weak-order SAT check (`relative_sat.py`), which allows any number of levels, is satisfiable. So
  what fails is the small number of levels, not relative separation. The tower gives every leaf its own
  level and makes each gap an independent random variable at a separated scale of its own,
  recursively: each stage strips one coordinate, and height `w + 1` is used.
- **Order information alone is no obstruction.** `order_colgen.py` solves exactly the LP asking whether
  some law on total orders of the middle leaves equalizes the laws of the induced "which piece is
  biggest" permutations. At `(0,4)` it is solved exactly with value `0` (`order_colgen_0_4.out`), by the
  deterministic "left dominates" order. That is the order used by the tower.

## What this changes

- Sizes, depths and the exact tail are a **dead observation for every Guba set**. By A.1 of
  `thompson-f-flow-certificate-observation-gate`, no transport rule reading them certifies
  non-amenability of `F`. Width 4 was the one place where the size node left a candidate for positive
  defect, and that candidate is now gone.
- The first case (sizes) of `thompson-f-non-idempotent-prefix-with-exact-tail-is-dead` holds at every
  width.
- A flow certificate must read more than the size and depth of each piece:
  - shape information that the tower cannot randomize. The tower fixes only `(n_v, e_v)`, and the shape
    `X_v` is an arbitrary tree with those numbers; or
  - joint information across the first `m + 1` trees that is finer than the piece vector, such as exact
    shapes.

  The tower does **not** decide exact middle shapes. That refinement remains open.

## Attempts

- **2026-09-19, swarm-0917-w17-w17-f-follow.** Found and proved (see the route). Before the tower,
  finite-level relative models were tried:
  - an LP with column generation over `{1..L}^n` levels (`relative_colgen.py`);
  - pointwise monotone-pair rules (`relative_rules.py`);
  - a weak-order SAT check (`relative_sat.py`).

  With `L <= 3` levels at `(0,4)` nothing survives the rules. The SAT check says weak orders with many
  levels do satisfy them, and `order_colgen.py` gives the exact order-only LP value `0`. That pointed to
  "one separated scale per leaf, with random gaps", and so to the tower.
