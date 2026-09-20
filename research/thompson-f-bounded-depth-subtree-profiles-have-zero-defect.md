---
rg: 2
id: thompson-f-bounded-depth-subtree-profiles-have-zero-defect
kind: claim
title: For every Guba set of Thompson's F and every fixed r, the observation that reads each prefix tree down to depth r together with the size and depth of every subtree rooted at depth at most r, and the tail exactly, has shadow defect zero; so a flow certificate must read shape information at unbounded depth
distinct_from:
  thompson-f-tree-size-observations-have-zero-defect: that is the case r = 0 (sizes and depths of whole prefix trees), proved at every width by the route thompson-f-tree-size-observations-via-tower-law; this reads the top r levels and the sizes and depths of all 2^r-scale subtrees, a strict refinement for every r >= 1, which that node and route leave open ("the tower does not decide exact middle shapes").
  thompson-f-non-idempotent-prefix-with-exact-tail-is-dead: that asks the question for every prefix invariant without an idempotent probability, and that class contains exact shape, so its full statement is equivalent to thompson-f-is-amenable; this settles it for every invariant that factors through a bounded-depth profile, and names what is left.
  thompson-f-prefix-observation-shadow-defect: that is the exact prefix shape, whose defect equals that of the identity; this is the increasing sequence of dead observations whose join is that observation, and it proves nothing about it.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills finite tree automata by an idempotent measure; the profiles here carry unbounded integers and no idempotent measure, and the law is the tower law, not an automaton pump.
  thompson-f-hierarchical-size-laws-die-at-width-four: that kills a class of shadow laws for r = 0; the law here is the tower law, outside that class, and the observation is finer.
artifacts:
  - experiments/thompson-f-bounded-depth-profiles-2026-09-17/refined_cut_check.py
  - experiments/thompson-f-bounded-depth-profiles-2026-09-17/refined_cut_check.out
---

**ESTABLISHED** through `thompson-f-bounded-depth-subtree-profiles-have-zero-defect-proof`. It is a
corollary of the tower lemma `thompson-f-tower-size-laws-have-zero-defect`, applied with deeper tops.
Agent-verified, not independently reviewed.

## Setting

The definitions (`M`, `ρ^η_s`, `D_λ`, `δ_λ`, and a rule reading `Ψ`) are those of
`thompson-f-flow-certificate-observation-gate`. `S = S_(m+1,m+d+1)`, `K = m + 2d`.

For a binary tree `t` and `r >= 0`:
- `τ_r(t)` is the shape of `t` cut at depth `r` (its carets of depth `< r`);
- `U_r(t)` is the leaves of `τ_r(t)`, left to right;
- `t_u` is the subtree of `t` at `u`.

The **depth-`r` profile** is `P_r(t) = ( τ_r(t), (|t_u|, dep t_u)_(u ∈ U_r(t)) )`. It determines the
size and depth of every subtree rooted at depth `<= r`. `P_0(t) = (|t|, dep t)`.

The observation is

`Π^(r)_K(y) = ( P_r(t_0), ..., P_r(t_(K−1)), t_K, t_(K+1), ... )`.

## Theorem

For all `m >= 0`, `d >= 1` and `r >= 0`, `δ_1(Π^(r)_K) = 0` for `S_(m+1,m+d+1)`. So `δ_λ(Π^(r)_K) = 0`
for every `λ >= 1`, and the same holds for every coarsening of `Π^(r)_K`.

By A.1 of the gate, no transport rule that reads a bounded-depth profile of the prefix trees
certifies non-amenability of `F`. This holds even with the whole tail read exactly.

## Proof idea (full proof in the route)

Replace the depth-`d` tops of the route `thompson-f-tree-size-observations-via-tower-law` by complete
depth-`(d + r)` tops, and hang the tower-law trees `X_v` at the `N = (m + 1) 2^(d+r)` leaves.
1. Every piece of `split_s Z` sits at a node of depth `<= d`. So it is complete to depth `>= r`, and its
   `τ_r` is the complete depth-`r` tree for every `s`.
2. The `2^r` depth-`r` descendants of the `m + d + 1` pieces cover consecutive dyadic leaf intervals.
   These form a cut with the same number `(m + d + 1) 2^r` of intervals for every word `s`.
3. On each such subtree, size and depth have the tower lemma's offset form.

So the observation is one fixed function of the tower vector of a cut. The cut-blind property then
equalizes the laws for all `s`.

## What this changes

- **The non-idempotent node is the root in disguise, minus this theorem.** Exact shape is itself an
  invariant with no idempotent probability, as `thompson-f-non-idempotent-prefix-with-exact-tail-is-dead`
  notes. So "every such `Q` is dead" contains `δ_1(π_K) = 0`. By
  `thompson-f-prefix-observation-is-lossless` that is `δ_1(id_M) = 0`, which is amenability of `F`.
  The genuine sub-question is which invariants strictly coarser than shape are dead. This theorem kills
  every invariant computed from `P_r` for one fixed `r`, for all `r`. That covers:
  - sizes and depths (`r = 0`);
  - the root split `(|L|, |R|)`;
  - the full size-and-depth table of every subtree to any bounded depth.
- **Where a certificate must live.** Since `P_r(t) = t` once `r >= dep t`, the observations
  `Π^(r)_K` increase to the exact prefix. By the lossless theorem the defect of the exact prefix is that
  of the identity. So `F` is non-amenable iff `δ_λ(π_K) > 0` for some Guba set and `λ > 1`, while
  `δ_1(Π^(r)_K) = 0` for every `r`. Any certificate therefore needs information
  that no bounded-depth size-and-depth table carries. Examples are arm lengths, or which leaf interval
  holds the mass at depth `> r`, with `r` unbounded.
- **New prerequisite (fails iff `F` is non-amenable).** Semicontinuity along the profile tower:
  `δ_1(π_K) <= liminf_r δ_1(Π^(r)_K)`. With this theorem it gives `thompson-f-is-amenable`. It is
  equivalent to the root, but it pins the failure mode: a family of laws that is near-optimal at depth
  `r` must stay near-optimal once shape below depth `r` becomes visible.

## Scope and next steps

- Arm lengths (`δ(a, b) = 1 + a`, and `1 + b`) are not functions of `P_r`, so they are not covered.
  - Sketch, not claimed: make the left and right arms of each `X_v` i.i.d. and uniform on a long
    window, independent of the tower. The arm of a depth-`r` subtree is then its offset `k` plus the
    arm of its first (resp. last) `X_v`. These first and last leaves are pairwise distinct across the
    intervals of a cut.
  - This only needs a realizability margin in the tower, `e_v >= log2(n_v + 1) + 2` and
    `n_v >= e_v + 2W`.
- Finite-state information of the `X_v`, added to `P_r`, is also not covered here.
