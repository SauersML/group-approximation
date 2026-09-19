---
rg: 2
id: thompson-f-tree-size-observations-via-tower-law
kind: route
title: Complete depth-d tops with tower-law subtrees at their leaves make every Guba-set piece an interval block, so the tower lemma equalizes the size-and-depth piece laws of all words and delta_1(Sigma_K) = 0 at every width
target: thompson-f-tree-size-observations-have-zero-defect
requires:
  - thompson-f-tower-size-laws-have-zero-defect
artifacts:
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.py
  - experiments/thompson-f-relative-levels-2026-09-17/tower_check.out
---

**Target.** For all `m >= 0` and `d >= 1`, `δ_1(Σ_K) = 0` for `S = S_(m+1,m+d+1)`, with `K = m + 2d` and
`Σ_K(y) = ((|t_0|, dep t_0), ..., (|t_(K−1)|, dep t_(K−1)), t_K, t_(K+1), ...)`. The definitions (the
defect `D_λ`, and `ρ^η_s(y) = η(s y)`) are those of `thompson-f-flow-certificate-observation-gate`, and
the conventions (words, `split`, caret count, depth with a leaf at depth `0`) are those of
`experiments/thompson-f-shadow-defect-2026-09-17/exact_tail_shadow_defect.py`.

**Requires.** `thompson-f-tower-size-laws-have-zero-defect` (the tower lemma).

## The shadow law

Fix `ε > 0`. Put `w = m + d`, `N = (m + 1) 2^d` and `c = 2^d`. Take `(n_v, e_v)_(v = 1..N)` from the tower
lemma with these `N`, `w`, `c` and with `ε / |S|`. Let `X_v` be a fixed tree with `n_v` carets and depth
`e_v`, which exists by the realizability part.

Let `Z = (t_0, ..., t_m, •, •, ...)`, where `t_a` is the complete depth-`d` binary tree whose `2^d` leaves
carry `X_v` for `v = a 2^d + 1, ..., (a + 1) 2^d`, in left-to-right order. So the leaves `1..N` are
numbered globally from left to right. `η` is the law of `Z`, which is finitely supported.

## Step 1: the defect is a sum of distances of split laws

Let `s ∈ S`. If `split_s z` is defined, then `z = s · split_s z`. Conversely, `z = s y` implies
`split_s z = y`, since `split_i` inverts `merge_i` on forests whose `i`-th tree is not a leaf. Hence, when
`split_s Z` is defined almost surely:
- `ρ^η_s(y) = P(Z = s y) = P(split_s Z = y)`, which is a probability vector;
- `Ψ_* ρ^η_s = law Ψ(split_s Z)`.

Take `μ = ρ^η_(s_0)` for a fixed `s_0`. Then `||(P − Q)_+|| = TV(P, Q)` gives

`δ_1(Σ_K) <= D_1(μ, η) = Σ_(s ∈ S) TV( law Σ_K(split_(s_0) Z), law Σ_K(split_s Z) )`.   (∗)

## Step 2: pieces are interval blocks

Let `s = (i_1, ..., i_d)`, with `i_1 <= ... <= i_d` and `i_j <= m + j − 1`.

**Claim.** Before the `j`-th split, the first `m + j` entries of the current forest are the subtrees of `Z`
at the nodes of an antichain `A_(j−1)`, listed left to right. That antichain has `m + j` nodes of depth
`<= j − 1` in the tops, and it covers all `N` leaves.

*Proof, by induction on `j`.* This holds for `j = 1`, with the roots. The split at `i_j <= m + j − 1`
acts on one of these entries. That entry is the subtree at a node of depth `<= j − 1 < d`, so it is a
caret of the complete top and the split is defined. It is replaced by the subtrees at the node's two
children, which gives `A_j`. The trivial tail is never touched. ∎

So `split_s Z = (p_0, ..., p_w, •, •, ...)`. Here `p_j` is the subtree of `Z` at the `j`-th node `x_j` of
`A_d`, whose depth is `h_j <= d`. The depth-`d` leaves below `x_j` form a dyadic block of `2^(d − h_j)`
consecutive leaves. The blocks of an antichain covering all leaves, in left-to-right order, are
consecutive intervals `I_0 < I_1 < ... < I_w` partitioning `1..N`. So the left endpoints form a cut
`a(s)` in the sense of the tower lemma, with `a_0 = 1`.

`p_j` is the complete depth-`(d − h_j)` tree with `X_v` hanging at its leaves, for `v ∈ I_j`. Therefore

`|p_j| = (2^(d − h_j) − 1) + Σ_(v ∈ I_j) n_v`,   `dep p_j = (d − h_j) + max_(v ∈ I_j) e_v`.

`tower_check.py` checks both formulas, and the interval property, with `split_word` on random explicit
forests for 13 pairs `(m, d)` up to width 5. The output `tower_check.out` shows 0 failures.

## Step 3: conclusion

For every `s`, `Σ_K(split_s Z)` is the concatenation of three parts:
- the piece vector `((|p_j|, dep p_j))_(j = 0..w)`;
- the constant `(0, 0)` at positions `w + 1..K − 1`;
- the constant all-leaf tail.

By Step 2, the piece vector is `Y(a(s), b(s), f(s))`, with `b_j = 2^(d−h_j) − 1 <= c` and
`f_j = d − h_j <= c`. By the cut-blind property of the tower lemma, every term of (∗) is at most
`ε / |S|`. So `δ_1(Σ_K) <= ε`. Since `ε` is arbitrary, `δ_1(Σ_K) = 0`. ∎

By A.1 of the gate, no rule reading `Σ_K` certifies ratio `> 1` for any Guba set. The same holds for
every coarsening of `Σ_K`, such as the middle sizes `Ψ_mid` of
`thompson-f-hierarchical-size-laws-die-at-width-four`.
