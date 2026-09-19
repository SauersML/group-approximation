---
rg: 2
id: leavitt-weighted-halves-have-dependent-commuting-pairs
kind: claim
title: For every positive weighting deg s_0 = p, deg s_1 = q of L_k(1,2), the nonnegative part is again a union of matrix rings over the free algebra, so a commuting pair whose bidegree support spans a cone missing the closed negative (or positive) quadrant is algebraically dependent
distinct_from:
  leavitt-nonnegative-part-is-matrix-union-over-free-algebra: that is the single weighting p = q = 1; this does every positive weighting, and so covers pairs of mixed standard degree, for example a = s_0 + s_0 t_1 t_1 of standard degrees 1 and -1.
  leavitt-homogeneous-commuting-pairs-are-algebraically-dependent: that needs each element homogeneous for the standard grading; this allows arbitrary inhomogeneous elements, provided the bidegree support satisfies a cone condition.
  leavitt-polynomial-pairs-move-to-the-nonnegative-part: that asks to move every commuting independent pair into the standard nonnegative part; this shows that no move is needed for pairs whose bidegree cone misses a closed quadrant, and so cuts that claim down to pairs whose cone meets both closed quadrants.
artifacts:
  - experiments/leavitt-mixed-centralizers-2026-09-17/check_weighted_blocks.py
  - experiments/leavitt-mixed-centralizers-2026-09-17/leavitt.py
---

**ESTABLISHED (unreviewed)** by `leavitt-weighted-halves-dependence-proof`. It rests on the established
(unreviewed) claims `leavitt-nonnegative-part-is-matrix-union-over-free-algebra`, Statement 3, and
`matrices-over-free-fields-have-no-trdeg-two-subfields`.

**Setup.**
- Let `k` be a field and `L = L_k(1,2)`, with `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1`.
- The relations are homogeneous for the `Z^2`-grading with `bideg s_0 = (1,0)`, `bideg s_1 = (0,1)` and
  `bideg t_i = -bideg s_i`. So `bideg(s_w t_v) = (#_0 w - #_0 v, #_1 w - #_1 v)`.
- The **bidegree support** `S(x) ⊂ Z^2` of `x ∈ L` is the set of bidegrees of its nonzero `Z^2`-homogeneous
  components.
- For real `α, β > 0` put `L^(α,β)_(>=0) = ⊕ { L_(m,n) : αm + βn >= 0 }`. The standard nonnegative part is
  `α = β = 1`.
- Let `Q_- = {(x,y) : x <= 0, y <= 0}` and `Q_+ = -Q_-` be the closed quadrants.

**Statement.**
1. **Weighted blocks.** Let `p, q >= 1` be integers and `φ(w) = p·#_0 w + q·#_1 w`. Every finite subset of
   `L^(p,q)_(>=0)` lies in a unital subalgebra `B ⊆ L` isomorphic to `M_n(k<x_0, x_1>)` for some `n`.
2. **Dependence.** Suppose `a, b ∈ L` commute. Let `K = cone(S(a) ∪ S(b))`. If `K ∩ Q_- = {0}` or
   `K ∩ Q_+ = {0}`, then `a` and `b` are algebraically dependent over `k`.
3. **Cone test.** For a finite `S ⊂ Z^2` with cone `K`, these are equivalent:
   - `K ∩ Q_- = {0}`;
   - `αm + βn >= 0` on `S` for some real `α, β > 0`;
   - the same for some integers `p, q >= 1`, so that every element with bidegree support in `S` lies in
     `L^(p,q)_(>=0)`.

**What it changes.**
- Consequence (c) of `leavitt-nonnegative-part-is-matrix-union-over-free-algebra` covers only pairs inside the
  standard half-planes `m + n >= 0` or `m + n <= 0`. This claim covers every pair whose bidegree cone misses a
  closed quadrant. That is a 2-parameter family of half-planes, closed under the swap `s_0 ↔ s_1`.
- Example. `a = s_0 + s_0 t_1 t_1` has standard degrees `1` and `-1`, and bidegrees `(1,0)` and `(1,-2)`. With
  `(p,q) = (3,1)` both weighted degrees are positive. So any commuting pair made of such elements is dependent.
- **Residual form of the transfer claim.** `leavitt-polynomial-pairs-move-to-the-nonnegative-part` is now needed
  only for commuting independent pairs whose bidegree cone meets both `Q_+ ∖ 0` and `Q_- ∖ 0`. The same holds for
  every pair of independent elements of `k[a,b]`, since each such pair must itself be of that kind.
- The residual is not empty as a set of elements. `s_0 + t_0` has `S = {(1,0), (-1,0)}`, whose cone meets both
  quadrants. `leavitt-polynomial-pairs-move-to-the-nonnegative-part` records the obstruction that stops every
  regrading from moving such elements.
