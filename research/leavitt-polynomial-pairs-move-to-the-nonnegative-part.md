---
rg: 2
id: leavitt-polynomial-pairs-move-to-the-nonnegative-part
kind: claim
title: If L_k(1,2) contains a polynomial ring in two variables, then so does its nonnegative graded part
distinct_from:
  leavitt-nonnegative-part-is-matrix-union-over-free-algebra: that describes the nonnegative part and handles pairs already inside it; this asks to move a mixed-degree pair into it.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that is the full rank statement; this is only the transfer between L and its nonnegative part, true for example if both sides have rank 1.
  laurent-tensors-reduce-leavitt-rank-to-function-fields: that transfers rank between coefficient fields; this transfers it between degree ranges of the Z-grading.
---

**OPEN.** Let `k` be a field and `L = L_k(1,2)`, Z-graded by `deg s_i = 1`. Suppose `L` contains commuting
`k`-algebraically independent `a, b`. Then `L_(>=0) = ⊕_(n >= 0) L_n` contains such a pair.

**Status of the pieces.**
- By the involution `s_i ↔ t_i`, it is enough to reach `L_(>=0)` or `L_(<=0)`.
- Pairs with `a, b ∈ L_(>=0)` or `a, b ∈ L_(<=0)` need nothing.
- `L_0` is ultramatricial, hence algebraic. So a pair inside `L_0` never occurs, and some member of any pair has a
  nonzero component of nonzero degree.

**Why it can fail on its own.** `L_(>=0)` is stably finite, while `L` is purely infinite
(`leavitt-nonnegative-part-is-matrix-union-over-free-algebra`, consequence (d)). So no homomorphism
`L → L_(>=0)` does the transfer. A commuting pair could in principle use the infinite part, with genuinely
two-sided degree support.

## Attempts

**w16: ideas that fail.**
- *Leading forms.* This would take top-degree components of elements of `k[a, b]`. It fails because `L` is not a
  graded domain: `(s_0 t_0)(s_1 t_1) = 0` in degree 0. So leading forms of a domain can multiply to zero.
- *Conjugation.* Conjugation by homogeneous units, and the corner maps `x ↦ s_w x t_w`, preserve degree. So they
  cannot shift a negative-degree support into `L_(>=0)`.
- *Filtration.* `L = ∪_N t_0^N L_(>=0)` is a filtration by one-sided `L_(>=0)`-modules, not by subalgebras. It
  bounds the negative support of `k[a, b]` but does not move it.

**w17 (2026-09-19): weighted halves, the residual, and an isotropy obstruction for regradings.**
- *Reduction (established).* `leavitt-weighted-halves-have-dependent-commuting-pairs` shows that for every
  weighting `deg s_0 = p`, `deg s_1 = q` with `p, q >= 1`, the nonnegative part is again a union of copies of
  `M_n(k<x_0, x_1>)`. The blocks are cut by the prefix code of first passage above weight `N`.
  - So a commuting pair needs no move when the cone of its `Z^2`-bidegree support misses a closed quadrant.
  - This claim is therefore needed only for **residual pairs**: pairs whose bidegree cone meets both
    `Q_+ ∖ 0` and `Q_- ∖ 0`.
  - Every independent pair inside `k[a, b]` must be residual too.
- *Obstruction (isotropy lag at a periodic point).* The invariant is defined as follows.
  - Let `p` be an eventually periodic infinite word with primitive period `z`.
  - For `x = Σ c_(w,v) s_w t_v`, put `ε_(p,m)(x) = Σ c_(w,v)`, summed over pairs with `w, v` prefixes of `p`,
    `σ^|w| p = σ^|v| p` and `|w| - |v| = m|z|`.
  - This is the value of `x`, viewed in the Steinberg algebra of the Cuntz groupoid, at the isotropy arrow of
    lag `m|z|` at `p`. It is well defined because it kills every refinement relation
    `s_w t_v = s_(w0) t_(v0) + s_(w1) t_(v1)`, and those relations span the kernel from formal sums to the
    normal-form basis.
  - For positive weights `φ`, any monomial counted by `ε_(p,m)` has weighted degree `m·φ(z)`. So `x` in the
    `φ`-nonnegative half forces `ε_(p,m)(x) = 0` for all `m < 0`.
  - Conjugation by an element `u ∈ V` moves isotropy at `u^(-1)p` to isotropy at `p` and keeps the lag. So
    `ε_(p,m)(u x u^*) = ε_(u^(-1)p, m)(x)`.
  - **Where every member dies.** Take any element with `ε_(p,m) ≠ 0 ≠ ε_(p,-m')` at a single point, with
    `m, m' >= 1`; for example `s_0 + t_0` at `p = 0^∞`. Conjugating by `V` and then choosing any positive
    weighting, of either sign, can never put it in a weighted half. This follows from the two facts above.
  - The same step kills regrading by any `Z`-valued cocycle that is nonzero on that isotropy arrow, since
    `c(γ^(-1)) = -c(γ)`.
  - So the residual cannot be removed by changing the grading. A proof of this claim for residual pairs has to
    use the commutation `ab = ba` in an essential way.
- *Census (computation, over `F_2`).* The scripts are `experiments/leavitt-mixed-centralizers-2026-09-17/`
  `census.py` and `pairs.py`.
  - They computed bounded-window centralizers `C_R(a)` (`|w|, |v| <= R <= 4`) of about 125 random transcendental
    mixed-degree elements `a` supported in `|w|, |v| <= 2`, 40 of them residual.
  - For each `b` in a basis of `C_3(a)`, and for random sums of two basis elements, they computed the rank of
    `{a^i b^j : i, j <= N}`.
  - Most centralizers equal `k[a]` in the window, for example for `s_0 + t_0` and `s_0 + t_1` up to `R = 4`.
  - Larger ones come from corners, for example `a = s_0 (s_0 + t_0) t_0`, whose centralizer contains
    `s_1 L t_1`, and all of those pairs have low-degree relations.
  - The one full-rank pair at `N = 3` is `a = s_0 t_(10) + s_(10) t_0 + s_(10) t_(00) + s_(10) t_(11)` with a
    partner of degrees `-2..0`. It has ranks `9, 16, 21` at `N = 2, 3, 4`, so it satisfies a relation of
    bidegree at most `(4, 4)`.
  - No candidate for `k[x, y]` appeared. Every rank grows linearly in `N`, as for commuting pairs of
    Gelfand–Kirillov dimension 1.
