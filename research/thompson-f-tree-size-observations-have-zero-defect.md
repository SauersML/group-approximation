---
rg: 2
id: thompson-f-tree-size-observations-have-zero-defect
kind: claim
title: For every Guba set S_(m+1,m+d+1) of Thompson's F, the observation that reads the sizes and depths of the first I+D+1 trees and every later tree exactly has shadow defect zero (proved at every width by a left-dominant iterated-exponential tower law, route thompson-f-tree-size-observations-via-tower-law; the scale-shift padding of Theorem 1 works only up to width 3)
distinct_from:
  thompson-f-non-idempotent-prefix-with-exact-tail-is-dead: that is the statement for every prefix invariant with no idempotent state measure at once; this is the one invariant (sizes, with depths) that it names first, proved here for the Guba sets of width at most 3 by an explicit padding, together with a precise obstruction showing where that padding stops. It is therefore a partial special case of that node and does not close it.
  thompson-f-exact-tail-observations-have-zero-defect: that kills the exact tail only when the prefix is read through an invariant carrying an idempotent probability, by a tower coupling; sizes carry no such measure, and the shadow law here is not a tower coupling but a scale-shift padding (a uniform global dyadic scale plus two huge end combs).
  thompson-f-flow-certificate-observation-gate: that supplies the definitions, Theorem A and A.1 used here, and lists dead observations that read no unbounded data of individual trees; its Scope leaves "sizes, depths, shapes" open, and this is a kill of sizes and depths for small width only.
  thompson-f-prefix-observation-shadow-defect: that asks for positive defect of the exact prefix shapes without the tail, and a positive answer proves non-amenability; this is a coarsening of the prefix in the prefix positions and a refinement in the tail, and proves nothing about that node.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills rules computed by a finite tree automaton; the size of a tree is not finite-state, and the padding here uses no automaton or pumping.
  thompson-f-monomial-doubling-ratio-depends-only-on-width: that is a statement about expansion ratios of Guba sets depending on the width; this is about which observations of a forest a transport rule may read. The only link is that the padding threshold found here is also a function of the width m+d alone.
artifacts:
  - experiments/thompson-f-size-observation-2026-09-17/verify_s24.py
  - experiments/thompson-f-size-observation-2026-09-17/verify_s24.out
  - experiments/thompson-f-size-observation-2026-09-17/equal_middle_lp.py
  - experiments/thompson-f-size-observation-2026-09-17/equal_middle_lp.out
  - experiments/thompson-f-size-observation-2026-09-17/equal_middle_lp_d1.out
  - experiments/thompson-f-size-observation-2026-09-17/prop_middle_fit.py
  - experiments/thompson-f-size-observation-2026-09-17/prop_middle_fit_both.out
  - experiments/thompson-f-size-observation-2026-09-17/prop_middle_fit_left.out
  - experiments/thompson-f-size-observation-2026-09-17/random_middle_lp.py
  - experiments/thompson-f-size-observation-2026-09-17/random_middle_lp.out
  - experiments/thompson-f-size-observation-2026-09-17/pattern_search.py
  - experiments/thompson-f-size-observation-2026-09-17/pattern_search.out
  - experiments/thompson-f-size-observation-2026-09-17/dyadic_search.py
  - experiments/thompson-f-size-observation-2026-09-17/dyadic_search.out
  - experiments/thompson-f-size-observation-2026-09-17/level_search.py
  - experiments/thompson-f-size-observation-2026-09-17/level_search.out
  - experiments/thompson-f-size-observation-2026-09-17/mixed_search.py
  - experiments/thompson-f-size-observation-2026-09-17/mixed_search.out
  - experiments/thompson-f-size-observation-2026-09-17/mixed_search_m2d2_c4.out
  - experiments/thompson-f-size-observation-2026-09-17/mixed_search_m1d3_c5.out
  - experiments/thompson-f-size-levels-2026-09-17/hierarchical_kill.py
  - experiments/thompson-f-size-levels-2026-09-17/hierarchical_kill.out
  - experiments/thompson-f-size-levels-2026-09-17/multilevel_lp.py
  - experiments/thompson-f-size-levels-2026-09-17/colgen_lp.py
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.py
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.out
---

**OPEN.** The boxed statement is proved for every Guba set of width `m + d <= 3`: Theorem 1 below,
with an explicit shadow law and a complete proof. It is open for width `>= 4`. There, Theorem 2 kills
the natural extension of the padding, the whole single-level class, at a named step. So the width-4
case needs a new kind of shadow law, or it is a genuine candidate for positive defect.

**Setting (verbatim from `thompson-f-flow-certificate-observation-gate`).** `M` is the positive monoid
of `F`, identified with forests `y = (t_0, t_1, ...)`. For finite `S ⊆ M` and `Ψ : M → X`, a rule reading
`Ψ` is `w(s, y) = G(s, Ψ(y))`, and for probability vectors `μ, η` on `M`, `ρ^η_s(y) = η(s y)`,

`D_λ(μ, η) = Σ_(s ∈ S) || (Ψ_* μ − λ Ψ_* ρ^η_s)_+ ||`,   `δ_λ(Ψ) = inf_(μ, η) D_λ(μ, η)`.

A.1 of the gate: if `δ_1(Ψ) = 0`, no rule reading `Ψ` is a certificate with ratio `> 1`.

**The observation.** For `S = S_(m+1,m+d+1)` we have `I = m + d − 1`, `D = d`, and `K = I + D + 1 = m + 2d`,
as in `thompson-f-exact-tail-observations-have-zero-defect`. Put

`Σ_K(y) = ( (|t_0|, dep t_0), ..., (|t_(K−1)|, dep t_(K−1)), t_K, t_(K+1), ... )`,

where `|t|` is the caret count and `dep t` the depth. This is the pair (prefix sizes and depths, exact
tail). It is the first open case listed by `thompson-f-non-idempotent-prefix-with-exact-tail-is-dead`.

**Boxed statement.** For all `m >= 0` and `d >= 1`, `δ_1(Σ_K) = 0` for `S = S_(m+1,m+d+1)`.

## 1. Two reductions (proved)

We use the conventions of `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py`.
Every `s ∈ S` is a word `(i_1, ..., i_d)`, `split_s = split_(i_d) ∘ ... ∘ split_(i_1)`, and for `Z ~ η`
the pushforward `Ψ_* ρ^η_s` is the law of `Ψ(split_s Z)`. In particular, if `split_s Z` is defined almost
surely for every `s`, then taking `μ = ρ^η_(s_0)` gives

`δ_1(Ψ) <= Σ_(s ∈ S) TV( law Ψ(split_(s_0) Z), law Ψ(split_s Z) )`.   (∗)

**Lemma 1 (only the first m+1 roots are cut; the tail shifts rigidly).** Words of `S_(m+1,m+d+1)`
correspond bijectively to rooted subforests `σ_s` with `d` carets on roots `0..m` (Catalan-type counts:
`|S| = 2, 5, 14, 42` for `m = 1` and `d = 1..4`, and `|S| = 9` for `m = d = 2`). If the first `m + 1` trees of
`z` contain `σ_s`, then

`split_s z = (p_0, ..., p_(m+d), t_(m+1), t_(m+2), ...)`,

where `p_0, ..., p_(m+d)` are the subtrees of `z` hanging from the `m + d + 1` leaves of `σ_s`, in left-to-right
order. *Proof.* Induction on `d`. A split at index `i` replaces the `i`-th entry by its two children. Every
letter of a word of `S_(m+1,m+d+1)` indexes an entry that came from roots `0..m`, which is the defining
property of the Guba set. The check `antichain` in `equal_middle_lp.py` asserts `m + d + 1` entries for
every word, and stage 2 of `exact_tail_shadow_defect.py` checks that later trees are untouched. ∎

So, for `Σ_K`, the positions `m + d + 1, ..., K − 1` hold the sizes and depths of `t_(m+1), ..., t_(m+d−1)`,
and the positions `>= K` hold the exact trees `t_(m+d), ...`. Both are the same for every `s`. If the tail
`(t_(m+1), ...)` is drawn independently of the first `m + 1` trees, then (∗) reduces to the following. For
every `s`, the law of the **piece vector** `((|p_j|, dep p_j))_(j = 0..m+d)` must be the same, up to `ε` in
total variation.

**Lemma 2 (x_0-reduction).** `S_(1,d+1) = x_0 · S_(2,d+1)`, meaning that every word of `S_(1,d+1)` starts
with the letter `0` and the rest is a word of `S_(2,d+1)`. Hence a shadow law for `S_(2,d+1)` whose first
two trees are `(a, b)` gives one for `S_(1,d+1)` with first tree `(a, b)` (one more caret), and conversely.
The observation windows match: `K(S_(1,d+1)) = 2d` and `K(S_(2,d+1)) = 2d − 1`, and positions shift by one
under the first split. *Proof.* On one root, the only possible first split is at `0`, and it leaves two
roots and `d − 1` carets. ∎

So the width `m + d` is the relevant parameter: `(0, d) ≡ (1, d − 1)`. The numerics below agree, and
every threshold found depends on `m + d` only.

## 2. Theorem 1: width at most 3 is dead (proved)

**Theorem 1.** `δ_1(Σ_K) = 0` for every `S_(m+1,m+d+1)` with `m + d <= 3`. It remains `0` if `Σ_K` is
refined further to read the **exact shapes** of the middle pieces, that is of positions `1, ..., m + d − 1`.

By Lemma 2 and the trivial case `S_(1,2) = {x_0}` (a single `s`, so (∗) is `0`), it is enough to treat
`(m, d) = (1, 1), (1, 2), (2, 1)`, i.e. `S_(2,3)`, `S_(2,4)` and `S_(3,4)`.

**The shadow law.**
- `T_j` is the complete binary tree of depth `j`, with `2^j − 1` carets.
- `C_n` is the left comb with `n` carets (for the right end we use the right comb, but the choice is
  irrelevant).
- `k` is uniform on `{1, ..., K_0}`, `n` and `n'` are uniform on `{L, ..., 2L}`, all independent, and
  the tail `(t_(m+1), ...)` is fixed, say all leaves.

| set | `t_0` | `t_1` | `t_2` |
|---|---|---|---|
| `S_(2,3)` | `(C_n, •)` | `(•, C_n')` | — |
| `S_(2,4)` | `((C_n, T_k), T_k)` | `(T_k, (T_k, C_n'))` | — |
| `S_(3,4)` | `(C_n, T_(k+1))` | `(T_k, T_k)` | `(T_(k+1), C_n')` |

**The piece vectors** are computed exactly by `verify_s24.py` (output `verify_s24.out`). There
`inf+c` denotes a piece consisting of the comb together with `c` extra carets.

- `S_(2,4)`: for each of the 5 words the pieces are `(C_n + c_0, T_j, T_j, C_n' + c_3)`, with
  `j ∈ {k − 1, k}`. It is `j = k` for the words `(0,0), (0,2), (1,2)` and `j = k − 1` for `(0,1), (1,1)`.
  The garbage satisfies `c_0, c_3 <= 2^(k+1)`.
- `S_(3,4)`: for all 3 words the middle is `(T_j, T_j)` with `j ∈ {k, k + 1}`.
- `S_(2,3)`: the middle is `(•)` for both words.

In every case the two end pieces are "one comb plus at most `2^(K_0+2)` carets". The comb hangs at the
extreme leaf, so the depth is also `n + O(K_0)`.

**Proof of Theorem 1.** Fix `s, s'`.
- The middle pieces of `split_s Z` are `(T_(k+e), T_(k+e))` with `e ∈ {−1, 0}` (or `{0, 1}`) depending
  only on `s`. So the law of their exact shapes is the image of a uniform `k` on a window of length `K_0`,
  shifted by at most `1`. Its total variation distance is at most `1/K_0`.
- The end piece is `C_n` with at most `2^(K_0+2)` carets attached below the comb or beside it. Its size
  is `n + c` and its depth is `n + c'` with `0 <= c, c' <= 2^(K_0+2)`, and `c, c'` are functions of `(s, k)`.
  Conditionally on `k`, the size-and-depth law of that end piece, for uniform `n` on `{L..2L}`, moves by
  at most `2^(K_0+3)/L` in total variation between `s` and `s'`.
- The pieces are conditionally independent given `k`, and Lemma 1 handles the tail.

So (∗) gives

`δ_1(Σ_K) <= |S| (1/K_0 + 2^(K_0+4)/L)`.

Let `L → ∞` first and then `K_0 → ∞`. ∎

Every `split_s` is defined almost surely, since the tops contain every `σ_s` (complete depth-`d` tops on
roots `0..m`). By A.1 of the gate, no rule reading `Σ_K` (or middle shapes) certifies ratio `> 1` for
these sets.

*Why it works.* The positions of the middle pieces are the same for all `s`. Only a **global dyadic
scale** differs, and a uniform scale absorbs it. Every piece that cannot be matched is dumped into one of
the two ends, where a huge comb absorbs it. This is a scale-shift coupling, not the tower coupling of
`thompson-f-exact-tail-observations-have-zero-defect`, which is why no idempotent measure is needed.

## 3. Theorem 2: the padding class dies at width 4 (class kill, proved for one class)

**The class `P` (single-level padding with absorbing ends).**
- The first `m + 1` trees have complete depth-`d` tops.
- The leftmost depth-`d` leaf of `t_0` and the rightmost depth-`d` leaf of `t_m` carry *absorbing atoms*:
  independent combs whose length is uniform on `{L..2L}` with `L → ∞`.
- Every other depth-`d` leaf `v` carries a subtree of size `λ w_v (1 + o(1))`. Here `λ` is a common scale
  mixed log-uniformly over a long range, and `w = (w_v) >= 0` is a fixed weight vector.

`W(x)` denotes the sum of `w_v` over the leaves `v` below the top node `x`. The size of a middle piece
`p_j(s)` is `λ W(p_j(s))`. A log-uniform scale and absorbing ends remove exactly the global factor and
nothing else. So a law in `P` drives (∗) for `Σ_K` to `0` iff

(P) the middle vector `v_s = (W(p_1(s)), ..., W(p_(m+d−1)(s)))` is nonzero for every `s`, and all the
`v_s` are proportional.

Theorem 1 is a law in `P`. For `S_(2,4)` the weights are `w = (2, 1, 1 | 1, 1, 2)` on the leaves
`01, 10, 11` of `t_0` and `00, 01, 10` of `t_1`, in units `2^(k−1)`.

**Theorem 2.** For width `m + d = 4` with `(m, d) = (0, 4)` or `(1, 3)`, that is `S_(1,5)` and `S_(2,5)`,
no weight vector satisfies (P). *Precise failure step:* the two subforests

`σ_C = {ε, 0, 00, 01}`  (middle pieces `001, 010, 011`)   and   `σ_E = {ε, 0, 00, 1}`  (middle pieces `001, 01, 10`)

share the first middle piece `001`, while the second middle piece of `σ_E` strictly contains that of
`σ_C`.

*Proof.* By Lemma 2, class `P` for `S_(2,5)` is class `P` for `S_(1,5)`, with the same tops and the same
pieces, so take `m = 0`, `d = 4` and one root. Write `v_s = a_s c` with a common `c = (c_1, c_2, c_3)`.

1. From `σ_C` and `σ_E`: `W(001) = a_C c_1 = a_E c_1` and `W(01) = W(010) + W(011)`. This gives
   `a_E c_2 = a_C (c_2 + c_3)`.
   - If `c_1 > 0`, then `a_C = a_E` and so `c_3 = 0`.
   - The mirror pair `{ε, 1, 11, 10}` (middle `100, 101, 110`) and `{ε, 1, 11, 0}` (middle `01, 10, 110`)
     share the *last* middle piece, and gives: if `c_3 > 0` then `c_1 = 0`.

   So `c_1 c_3 = 0`. By the mirror symmetry, take `c_3 = 0`.
2. Then the third middle piece has weight `0` for every `s`.
   - `{ε, 0, 1, 01}` has middle `010, 011, 10`, so `W(10) = 0`.
   - `{ε, 1, 10, 11}` has middle `100, 101, 110`, so `W(110) = 0`.
3. Now `{ε, 1, 10, 100}` has middle `1000, 1001, 101`. All three lie below `10`, so `v_s = 0`, which
   contradicts (P). In the mirror case `c_1 = 0`, the same contradiction comes from `{ε, 0, 01, 011}`. ∎

**Random weights (partial).** If `w` is random (independent of `λ`), (P) becomes "the law of the
direction `[v_s]` is the same for every `s`". Step 1 survives in the following form.
- `φ_C = W(001)/(W(001)+W(010))` and `φ_E = W(001)/(W(001)+W(01))` satisfy `φ_E <= φ_C` pointwise.
- Equal laws together with pointwise domination force equality almost surely.
- Therefore `W(001) · W(011) = 0` almost surely. The event where they are undefined is handled by
  `P(x + y = 0) = P(x + y + z = 0)` and `v_s ≠ 0`.

The full random case is **not** proved. `random_middle_lp.py` finds by exact LP that no mixture of weight
vectors in `{1, 2}^14` works for `(0, 4)`. The minimum total violation is `8.833` (summed over the 14
words), whereas it is `0` for `(0, 3)` and `(1, 2)`.

**Numerics for the whole class** (files `equal_middle_lp.out`, `equal_middle_lp_d1.out`,
`prop_middle_fit_both.out`, `prop_middle_fit_left.out`):

| `(m, d)` | width | equal middle, LP | proportional middle, best `max |log residual|` |
|---|---|---|---|
| (0,2), (1,1) | 2 | feasible | — |
| (0,3), (1,2), (2,1) | 3 | feasible | `4.2e-10`, `4.2e-10`, `3.2e-10` |
| (0,4), (1,3) | 4 | infeasible | `0.363`, `0.363` (Theorem 2) |
| (2,2), (3,1) | 4 | infeasible | `0.367`, `0.363` |
| (1,4), (2,3), (4,1) | 5 | infeasible | not run |

The variant with an absorbing atom at the left end only already fails at width 3 (`0.257` for `(0, 3)`).
So two absorbing ends are needed. The exhaustive tree-pattern searches (`pattern_search`,
`dyadic_search`, `level_search`, `mixed_search`, with outputs in `.out` files) find hits exactly in the
feasible rows and none elsewhere within their caret bounds. This includes "independent levels" (each
atom on its own log-uniform scale), which already dies at `(0, 3)`: there are 0 candidates there.

**What Theorem 2 kills and what it does not.** It kills every shadow law for `Σ_K` that is a
single-level padding with two absorbing ends at width 4. It does **not** kill:
- padding with several stable levels and middle pieces at different levels. The scouting analysis in
  the Attempts section argues that such mixed patterns are forced back to one middle level, but this is
  not written as a proof;
- random weights in general;
- tops that are not complete, or absorbing atoms elsewhere;
- non-padding laws.

`(2, 2)` and `(3, 1)` rest on numerics only.

## 4. What this changes

- The first case of `thompson-f-non-idempotent-prefix-with-exact-tail-is-dead`, prefix sizes and depths,
  is **dead for width at most 3**, by a coupling of a new type: a global dyadic scale shift with
  absorbing end combs. The idempotent-measure obstruction named by the 2026-09-17 referee is therefore
  not a real barrier for sizes: sizes admit a scale-invariant law instead of an idempotent one.
- At width 4 the natural extension of that coupling provably fails (Theorem 2), with the numerics
  matching exactly. Width 4 is the first width at which the size observation is a live candidate for
  **positive** defect. A positive answer would be a flow certificate reading only sizes, depths and the
  tail, and by A.3 of the gate it would prove `thompson-f-is-not-amenable`. That is the bounty-relevant
  open question this node leaves.
- Next falsifiable step: decide (P) for multi-level stable paddings at `(0, 4)`, where each level is a
  common stable scale and the weights at each level are proportional. Alternatively, find a
  non-padding law, for example one where the absorbing atoms sit at interior leaves chosen at random.

## Attempts

- **2026-09-19, swarm-0917-w15-w15-f-follow.**
  - *Found:* Lemma 1 (only roots `0..m` are cut and the tail shifts rigidly), Lemma 2 (the
    `x_0`-reduction), Theorem 1 (width at most 3 is dead, explicit law, checked by `verify_s24.py`) and
    Theorem 2 (single-level padding with absorbing ends dies at width 4, with the precise
    `σ_C`/`σ_E` domination step).
  - *Scouting, not proved:* in a leveled padding, a top node `x` whose address contains both a `0` and a
    `1`, at depth `h < d`, appears as a piece at every position in `[ones(x), ones(x) + d − h]` for
    suitable `s`. This forces the levels along positions `1..m+d−1` to be constant, i.e. a single middle
    level, as in class `P`, up to lower-level garbage absorbed by the ends. If written out, this would
    extend Theorem 2 to all multi-level stable paddings with absorbing ends.
  - *Dead end recorded:* independent log-uniform scales per atom (the "independent levels" of
    `mixed_search.py`) die already at `(0, 3)`. The comb-and-dyadic search with at most 2 carets
    finds nothing at `(1, 3)`.
- **2026-09-19, swarm-0917-w16-w16-f-follow.**
  - *Found (new node `thompson-f-hierarchical-size-laws-die-at-width-four`, with proof route):* the
    scouting item above, written out and extended. At **every** width `m + d >= 4` (including `(2,2)` and
    `(3,1)`, which rested on numerics), no *hierarchical* law makes the laws of the middle piece sizes
    agree. Hierarchical means finitely many levels with separated deterministic windows; levels, tight
    weights and per-level scales may be random and arbitrarily dependent; ends and tail are free. Complete
    tops are forced, not assumed (`P(T) >= 1 − D`). The proof has four steps. Domination at a common
    position forces max-level equalities. Equal laws propagate coordinate equalities, and a Boolean
    thresholding check (`hierarchical_kill.py`) collapses all middle leaves to one level. Then a
    *ratio pair* (a shared node at one middle position, strict nesting at another) contradicts equal
    laws of the scale-free ratio. Widths `>= 5` embed a width-4 base.
  - *Sharp:* at width 3 every step goes through except the ratio pair, which does not exist; Theorem 1's
    law lies in the class.
  - *Consequence for this node:* a zero-defect law at width `>= 4` must have some middle size ratio that
    is neither tight nor separated (overlapping scale windows). Theorem 1's mechanism cannot extend. The
    node stays **OPEN**. Next step: decide overlapping-window laws at `(0,4)`, e.g. i.i.d. log-uniform
    leaf sizes on a common range with absorbing ends, where the defect is a continuous optimisation over
    the log-size law, or prove positive defect against them.
  - *Numerics:* multi-level LP (`multilevel_lp.py`, `colgen_lp.py`) agrees. It is feasible at width 3 with
    weights `{1,2}`, and at `(0,4)` with one level the exact minimum violation is `5.263`.

- **2026-09-19, swarm-0917-w17-w17-f-follow.**
  - *Found:* the boxed statement holds at **every** width. It is now ESTABLISHED through the route
    `thompson-f-tree-size-observations-via-tower-law`, which requires the new claim
    `thompson-f-tower-size-laws-have-zero-defect` (proof in `thompson-f-tower-size-laws-have-zero-defect-proof`).
    The body above ("OPEN", "open for width `>= 4`", "candidate for positive defect") predates this and
    is superseded.
  - *The law.* It uses complete depth-`d` tops. At the `N = (m+1) 2^d` leaves, in global left-to-right
    order, it hangs trees with `n_v` carets and depth `e_v`, and the tail is trivial.
    - The sizes are `n_v = 2^(λ + D_v) + Unif{0..2^(λ + D_v) − 1}`.
    - `λ` is uniform on a long window.
    - `D_v = Σ_(i >= v) g_i`, with gaps `g_i = G + n'_i`, where `n'` is an independent copy of the same
      construction one stage lower. There are `m + d + 1` stages, and the last has constant gaps.
    - The depths are an independent tower of the same kind.
  - *Why it works.* Every piece of `split_s z` is a block of consecutive leaves, and its size is
    dominated by its leftmost leaf. The size vector is therefore a fixed kernel of the log-scales
    `λ + D_(a_j)`. The uniform `λ` absorbs one of them, and the gaps between them are the same problem
    one stage lower with one coordinate fewer. Depths are `d − h_j + e_(a_j)` by dominance.
  - *Checks.* `tower_check.py` checks the interval structure, the size and depth formulas via
    `split_word`, and realizability, for 13 pairs `(m, d)` up to width 5, with 0 failures.
  - *Relation to earlier kills.* Theorem 2 here and the class-`H` kill of
    `thompson-f-hierarchical-size-laws-die-at-width-four` stay valid. The tower is outside both, because
    its scale cluster sits at a random height, so no deterministic window separates its levels. The
    consequence drawn in the w16 entry above ("some middle size ratio neither tight nor separated") is
    false: in the tower every ratio is separated.
  - *Consequence.* By A.1 of the gate, sizes, depths and the exact tail give no flow certificate for any
    Guba set. The width-4 positive-defect candidate is dead. Exact middle shapes remain undecided at
    width `>= 4`.
