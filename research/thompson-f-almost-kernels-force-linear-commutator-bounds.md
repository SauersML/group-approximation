---
rg: 2
id: thompson-f-almost-kernels-force-linear-commutator-bounds
kind: claim
title: When a fixed nontrivial element of Thompson's F is almost the identity on a permutation pair, the pair almost commutes, linearly in the defects
distinct_from:
  thompson-f-following-models-separate-iff-mean-charges-commutator: that shows for invariant means on F-sets that a nontrivial kernel forces zero separation; this is a finitary linear inequality for every permutation pair and every fixed nontrivial word, with no F-set.
  thompson-f-sofic-iff-relator-system-unstable: that bounds separation only in the limit, through the character classification; this gives constants valid for all n on the pairs where a fixed nontrivial word nearly vanishes.
  thompson-f-sofic-iff-defect-to-separation-ratio-vanishes: that shows a witness only needs defect small relative to separation; this shows that on pairs where a fixed nontrivial word is almost trivial, defect is never small relative to separation.
artifacts:
  - research/artifacts/hl-f-sofic-relator-instability-2026-09-14.md
---

**ESTABLISHED (unreviewed).** Let `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]` and
`R_2 = [ab^-1, a^-2ba^2]`, and let `d` be the normalized Hamming distance.

**Statement.** Let `w` be a word in `a, b` representing a nontrivial element of `F`. There are integers
`N_w ≥ 0` and `M_w ≥ 1` such that for all `n` and all `A, B ∈ Sym(n)`,

`d(AB, BA) ≤ N_w · max_j d(R_j(A,B), 1) + M_w · d(w(A,B), 1)`.

Any expression of `[a,b]` in the free group as a product of conjugates of `R_1^±1`, `R_2^±1` and
`w^±1` gives such constants, as the numbers of relator factors and of `w`-factors, and one exists.

**Instances.**
- **Bounded order.** If `A^L = 1`, then `d(AB, BA) ≤ N_(a^L) · D(A,B)` with
  `D = max_j d(R_j(A,B),1)`, and the same holds for `B^L = 1` with `N_(b^L)`. Both words are nontrivial,
  since `x_0` and `x_1` have infinite order. So pairs with a generator of bounded order satisfy the
  separation inequality with a linear constant.
- **Almost laws.** If `d(w(A,B), 1) ≤ β` for a fixed nontrivial `w`, then
  `d(AB, BA) ≤ N_w D + M_w β`.
- **Witnesses move every element.** A family with `D_k → 0` and `d(A_kB_k, B_kA_k) ≥ ε` has
  `liminf d(w(A_k,B_k), 1) ≥ ε/M_w` for every nontrivial `w`. A family with `D_k/t_k → 0`, as in
  `thompson-f-sofic-iff-defect-to-separation-ratio-vanishes`, has
  `d(w(A_k,B_k),1) ≥ t_k (1 - N_w D_k/t_k)/M_w`.

**Scope.** Elementary. The one import is that every nontrivial normal subgroup of `F` contains `[F,F]`.
The constants are not computed. In the limit the character classification gives the sharper bound
that every `g ≠ e` moves mass at least `t`. This claim is the finitary counterpart, with a linear
rate at every `n`. It decides nothing about `thompson-f-is-sofic`.

Proof route: `thompson-f-almost-kernels-force-linear-commutator-bounds-proof`.
