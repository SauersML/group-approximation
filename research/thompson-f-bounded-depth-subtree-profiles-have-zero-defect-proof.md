---
rg: 2
id: thompson-f-bounded-depth-subtree-profiles-have-zero-defect-proof
kind: route
title: Complete depth-(d+r) tops refine every Guba-set piece into 2^r dyadic leaf intervals, one cut of (m+d+1)2^r intervals per word, so the tower lemma equalizes the depth-r profile laws of all words
target: thompson-f-bounded-depth-subtree-profiles-have-zero-defect
requires:
  - thompson-f-tower-size-laws-have-zero-defect
artifacts:
  - experiments/thompson-f-bounded-depth-profiles-2026-09-17/refined_cut_check.py
  - experiments/thompson-f-bounded-depth-profiles-2026-09-17/refined_cut_check.out
---

**Target.** `δ_1(Π^(r)_K) = 0` for `S = S_(m+1,m+d+1)`, all `m >= 0`, `d >= 1`, `r >= 0`. Notation is
that of the target. The conventions (words, `split`, caret count `|·|`, depth with a leaf at depth `0`)
are those of `experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py`.

**Requires.** The tower lemma `thompson-f-tower-size-laws-have-zero-defect`, used verbatim. For `N`
ordered leaves, `w + 1` intervals and offsets in `{0..c}`, it gives a finitely supported law of
`(n_v, e_v)_(v <= N)` with two properties:
- **realizable:** there is a tree with `n_v` carets and depth `e_v`;
- **cut-blind:** for any two cuts with `w + 1` intervals and any offsets, the laws of
  `Y(a, b, f) = (b_j + Σ_(v ∈ I_j) n_v, f_j + max_(v ∈ I_j) e_v)_j` are within `ε` in total
  variation.

## The shadow law

Fix `ε > 0` and put:
- `N = (m + 1) 2^(d+r)`;
- `W = (m + d + 1) 2^r` intervals, so `w = W − 1`;
- `c = 2^(d+r)`.

Note `W <= N`, since `m + d + 1 <= (m + 1) 2^d`.

Take `(n_v, e_v)` from the tower lemma with these parameters and `ε / |S|`, and fix trees `X_v` with
`n_v` carets and depth `e_v`. Let `Z = (t_0, ..., t_m, •, •, ...)`, where `t_a` is the complete
depth-`(d + r)` tree with `X_v` at its leaves for `v = a 2^(d+r) + 1, ..., (a + 1) 2^(d+r)`, in order.
Let `η` be the law of `Z`.

## Step 1 (as Step 1 of `thompson-f-tree-size-observations-via-tower-law`)

Suppose `split_s Z` is defined almost surely for every `s`. Then `Ψ_* ρ^η_s = law Ψ(split_s Z)`, and
`μ = ρ^η_(s_0)` gives

`δ_1(Π^(r)_K) <= Σ_s TV( law Π^(r)_K(split_(s_0) Z), law Π^(r)_K(split_s Z) )`.   (∗)

## Step 2: pieces and their depth-r descendants

Let `s = (i_1, ..., i_d)` be in normal form, so `i_j <= m + j − 1`.

**Pieces.** The induction of Step 2 of that route applies word for word. Before the `j`-th split, the
first `m + j` entries are the subtrees at an antichain of top nodes of depth `<= j − 1`. That depth is
`< d + r`, so the split is defined and cuts a caret of a top. So `split_s Z = (p_0, ..., p_(m+d), •, ...)`
with `p_j` the subtree at a top node `x_j` of depth `h_j <= d`. The nodes `x_0 < ... < x_(m+d)` form an
antichain that covers all `N` leaves.

**Profiles of the pieces.** `p_j` is the complete tree of depth `d + r − h_j >= r` with `X_v` hung below.
- Hence `τ_r(p_j)` is the complete depth-`r` tree, the same for every `s`.
- `U_r(p_j)` is the `2^r` depth-`r` descendants of `x_j`, left to right.
- The subtree at each `u ∈ U_r(p_j)` is the complete tree of depth `k_j = d − h_j` with `X_v` hung at
  its leaves. Its leaves form a dyadic interval `I_u` of `2^(k_j)` consecutive leaves.

So

`|(p_j)_u| = (2^(k_j) − 1) + Σ_(v ∈ I_u) n_v`,   `dep (p_j)_u = k_j + max_(v ∈ I_u) e_v`.

**The refined cut.** The depth-`r` descendants of an antichain that covers all leaves again form such
an antichain. So the `W` intervals `I_u`, listed piece by piece and left to right within each piece, are
consecutive and partition `1..N`. Their left endpoints form a cut `a'(s)` with `W` intervals. The
offsets are `b_u = 2^(k_j) − 1 <= c` and `f_u = k_j <= c`.

**Check.** `refined_cut_check.py` verifies (a) to (e) of its docstring for every word of `S_(m+1,m+d+1)`
at 12 triples `(m, d, r)` with `r <= 3` and `N <= 64`:
- splits never go below the tops;
- there are `m + d + 1` pieces;
- the depth-`r` tops are complete;
- the `W` intervals partition `1..N` in order;
- the two formulas above hold, with explicit random `X_v`, and the pieces agree with the repository's
  `split_word`.

The output `refined_cut_check.out` shows 0 failures.

## Step 3: conclusion

For every `s`, `Π^(r)_K(split_s Z) = Φ( Y(a'(s), b(s), f(s)) )`. Here `Φ` is one fixed map, the same
for all `s`. It cuts the `W` coordinate pairs into `m + d + 1` consecutive blocks of `2^r`, and turns
each block into a profile with the complete depth-`r` shape `τ_r`. It then appends
`P_r(•) = (•, (0, 0))` at positions `m + d + 1, ..., K − 1`, and the all-leaf tail.

`Φ` is fixed because the number of pieces and the block length do not depend on `s`. Total variation
does not increase under a fixed map. So by cut-blindness every term of (∗) is at most `ε / |S|`, and
`δ_1(Π^(r)_K) <= ε`. Since `ε` is arbitrary, `δ_1(Π^(r)_K) = 0`.

`D_λ` is nonincreasing in `λ`, so `δ_λ = 0` for `λ >= 1`. Coarsenings follow by A.4 of the gate. ∎
