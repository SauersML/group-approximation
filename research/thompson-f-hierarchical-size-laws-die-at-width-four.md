---
rg: 2
id: thompson-f-hierarchical-size-laws-die-at-width-four
kind: claim
title: For every Guba set of Thompson's F of width m+d at least 4, no scale-separated (hierarchical) law of the subtrees below the tops drives the defect of the middle piece sizes to zero, so every zero-defect law for sizes must have middle size ratios that are neither tight nor separated; width 3 is the sharp threshold
distinct_from:
  thompson-f-tree-size-observations-have-zero-defect: that proves zero defect of prefix sizes and depths for width at most 3 and kills the single-level padding class P at width 4 for (0,4) and (1,3) only; this kills the much larger hierarchical class H (any number of separated levels, random levels, random tight weights, random per-level scales, any dependence, interior atoms) at every width at least 4, including (2,2) and (3,1), which rested on numerics there. It does not decide that node, which asks about all laws.
  thompson-f-flow-certificate-observation-gate: that supplies the defect D_lambda and the shadow-defect criterion; this is a class kill for one observation (middle piece sizes) and every refinement of it, and proves nothing about positive defect.
  thompson-f-non-idempotent-prefix-with-exact-tail-is-dead: that is the statement for every prefix invariant without an idempotent measure; this shows that for sizes the only surviving zero-defect laws at width at least 4 are non-hierarchical, a restriction on any proof of that node for its first case.
  thompson-f-exact-tail-observations-have-zero-defect: that kills the exact tail through invariants carrying an idempotent probability by a tower coupling; sizes carry none, and this concerns scale-separated padding laws, not tower couplings.
  thompson-f-markov-size-chain-vectors-saturate-in-the-scale-limit: that studies Markov size-chain test vectors for the norm of the Kesten operator; this concerns laws of forests making Guba-set split laws agree, a different (dual, flow) question.
artifacts:
  - experiments/thompson-f-size-levels-2026-09-17/hierarchical_kill.py
  - experiments/thompson-f-size-levels-2026-09-17/hierarchical_kill.out
  - experiments/thompson-f-size-levels-2026-09-17/multilevel_lp.py
  - experiments/thompson-f-size-levels-2026-09-17/colgen_lp.py
---

**ESTABLISHED** (agent-verified; proof in `thompson-f-hierarchical-size-laws-die-at-width-four-proof`).

**Setting (verbatim from `thompson-f-flow-certificate-observation-gate`).** `M` is the positive monoid
of `F`, identified with forests `y = (t_0, t_1, ...)`. For finite `S ⊆ M` and `Ψ : M → X`, and for
probability vectors `μ, η` on `M`, `ρ^η_s(y) = η(s y)`,

`D_λ(μ, η) = Σ_(s ∈ S) || (Ψ_* μ − λ Ψ_* ρ^η_s)_+ ||`,   `δ_λ(Ψ) = inf_(μ, η) D_λ(μ, η)`.

**Guba sets (verbatim from Lemma 1 of `thompson-f-tree-size-observations-have-zero-defect`).** Words of
`S = S_(m+1,m+d+1)` correspond bijectively to rooted subforests `σ_s` with `d` carets on roots `0..m`. If
the first `m + 1` trees of `z` contain `σ_s`, then `split_s z = (p_0, ..., p_(m+d), t_(m+1), t_(m+2), ...)`,
where `p_0, ..., p_(m+d)` are the subtrees of `z` hanging from the `m + d + 1` leaves of `σ_s`, in
left-to-right order. The **width** is `w = m + d`; the **middle positions** are `1, ..., w − 1`.

**The observation.** `Ψ_mid(y) = (|t_1|, ..., |t_(w−1)|)`, the caret counts of trees `1..w−1`. It is a
coarsening of the prefix observation `Σ_K` of `thompson-f-tree-size-observations-have-zero-defect`
(there `K = m + 2d > w − 1`), and of every observation that reads these sizes.

**Complete tops are forced.** Put `D_n = D_1(μ_n, η_n)` for `Ψ_mid` and `Z_n ~ η_n`. Let `T` be the event
that each of the first `m + 1` trees of `Z_n` contains the complete depth-`d` top (every caret of depth
`< d`). Step 1 of the proof shows `P(T) >= 1 − D_n`, and that the sub-probability laws
`ν_s = law(Ψ_mid(split_s Z_n); T)` satisfy `||ν_s − ν_(s')|| <= 6 D_n` for all `s, s'`. On `T`, write `X_v`
for the subtree of `Z_n` hanging at a depth-`d` leaf `v` of the tops. The two **extreme** leaves (leftmost
of root `0`, rightmost of root `m`) always lie in the end pieces `p_0`, `p_w`. Every other depth-`d` leaf
is **middle**, and only these enter `Ψ_mid`.

**The hierarchical class `H`.** A sequence `η_n` is in `H` if, for some fixed `L >= 1`, on `T` there are
random variables (any joint law, any dependence on each other and on anything else):
- a **level** `ℓ_n(v) ∈ {0, 1, ..., L}` and a **weight** `c_n(v) > 0` for every middle leaf `v`;
- **scales** `Λ_(1,n), ..., Λ_(L,n) > 0`;

and deterministic thresholds `θ_(1,n) <= θ_(2,n) <= ... <= θ_(L,n)` with `θ_(1,n) → ∞`, such that, as `n → ∞`
and conditionally on `T`:
- (H1) the families `c_n(v)` and `1 / c_n(v)` are tight;
- (H2) `|X_v| · 1{ℓ_n(v) = 0}` is tight (level `0` means bounded size);
- (H3) `(|X_v| / Λ_(ℓ(v),n) − c_n(v)) · 1{ℓ_n(v) >= 1} → 0` in probability;
- (H4) scale separation: `Λ_(ℓ,n) / θ_(ℓ,n) → ∞` and `Λ_(ℓ,n) / θ_(ℓ+1,n) → 0` in probability (the second for `ℓ < L`).

Nothing is assumed about the end pieces, the extreme leaves, or the tail `t_(m+1), ...`.

**Theorem.** Let `w = m + d >= 4` and `d >= 1`. For every sequence `η_n` in `H` and every `μ_n`,
`D_1(μ_n, η_n)` for `Ψ_mid` does **not** tend to `0`. The same holds for every refinement of `Ψ_mid`, in
particular for `Σ_K` and for the exact shapes of the middle pieces.

**Sharpness.** At width `3` the class `H` contains a zero-defect law: Theorem 1 of
`thompson-f-tree-size-observations-have-zero-defect` is in `H` with `L = 1`, deterministic weights
`(2,1,1 | 1,1,2)` for `S_(2,4)`, scale `Λ = 2^(k−1)`, `k` uniform on `{1..K_0}`, and `θ_1 = 2^(√K_0)`. The
mechanical check below confirms that, at width 3, every step of the proof goes through except the last
(no ratio pair exists).

(If `P(T) = 0` then `D_n >= 1` by Step 1, so `T` has positive probability whenever `D_n < 1`.)

## Where every hierarchical law dies

Only four facts about the Guba set are used, all about **middle** pieces (so the ends may absorb
anything). They are checked mechanically by `hierarchical_kill.py` (output `hierarchical_kill.out`) on
Boolean level functions, which suffices because thresholding `[ℓ >= t]` preserves every identity of the
form `max_A ℓ = max_B ℓ`:

1. **Domination.** If the same position `j` holds nodes `x ⊋ y` for two words, then `ℓ(x) >= ℓ(y)`
   pointwise while the laws agree, so `ℓ(x) = ℓ(y)` almost surely (`ℓ(x)` = max level below `x`).
2. **Law propagation.** If two coordinates of one word's middle level vector agree for every admissible
   level function, they agree for every word.
3. **Collapse.** After the fixpoint of 1 and 2 only constant level functions survive: all middle leaves
   carry one common (random) level `ℓ*`.
4. **Ratio pair.** Two words share the node `x` at one middle position `i` and have nodes `y ⊋ y'` at
   another middle position `j`. On `{ℓ* >= 1}` the scale-free ratio `|x| / (|x| + |p_j|)` is strictly
   smaller for the first word in the limit, contradicting equal laws. On `{ℓ* = 0}` the tight size at a
   domination position is strictly larger for one word, again contradicting equal laws.

| `(m, d)` | width | words | middle leaves | domination pairs | collapse | ratio pair (position `i` shared, `j` nested) | verdict |
|---|---|---|---|---|---|---|---|
| (0,4) | 4 | 14 | 14 | 50 | yes | `01` at 3; `001 ⊋ 0011` at 2 | killed |
| (1,3) | 4 | 14 | 14 | 50 | yes | `0:1` at 3; `0:01 ⊋ 0:011` at 2 | killed |
| (2,2) | 4 | 9 | 10 | 28 | yes | root `1` at 3; `0:1 ⊋ 0:11` at 2 | killed |
| (3,1) | 4 | 4 | 6 | 6 | yes (3 rounds) | root `2` at 3; root `1 ⊋ 1:1` at 2 | killed |
| (4,1), (3,2), (2,3) | 5 | 5, 14, 28 | 8, 14, 22 | 12, 96, 322 | yes | exists | killed |
| (0,3), (1,2), (2,1) | 3 | 5, 5, 3 | 6, 6, 4 | 4, 4, 2 | yes | **none** | survives (Theorem 1) |

Every width `>= 4` reduces to the four width-4 rows by embedding (Step 5 of the proof). So the obstruction
is exactly the ratio pair, which first exists at width 4.

## What this kills and what survives

Killed at every width `>= 4`, for the sizes of the middle pieces and for every refinement of them:
- the whole single-level class `P` of Theorem 2 of `thompson-f-tree-size-observations-have-zero-defect`
  whenever its zero-weight leaves are tight or sit in a separated window, now also for `(2,2)`, `(3,1)` and
  every larger width, where it rested on numerics;
- random tight weights in general (the partial case left open there);
- multi-level stable paddings with any number of separated levels, and random levels (which leaf is
  at which level may be random and correlated with everything);
- absorbing atoms at random interior leaves, as long as their size is in a separated window;
- any law of the ends and of the tail.

Not killed (the exact survivors): laws in which some ratio of middle-piece sizes is neither tight in
`(0, ∞)` nor tending to `0` or `∞`, i.e. with **overlapping scale windows**. Examples are independent
log-uniform sizes on a common long range, and continuous multi-scale mixtures. Any zero-defect law for
sizes at width `>= 4` must be of this kind, and any proof of positive defect must defeat such laws.
So this is a precise obstruction for one whole approach (scale-separated padding, the mechanism of
Theorem 1) and a sharp description of the remaining search space. It does not prove positive defect, so
it does not decide `thompson-f-tree-size-observations-have-zero-defect` or `thompson-f-is-amenable`.

**Supporting numerics** (`multilevel_lp.py`, `colgen_lp.py`; exact LP over finite multi-level models,
consistent with the theorem): `(0,3)` and `(1,2)` with one level and weights `{1,2}` are feasible (value 0);
`(0,4)` with one level has exact minimum violation `5.263` (count-only weights) by column generation.
