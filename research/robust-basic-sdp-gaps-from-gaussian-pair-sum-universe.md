---
rg: 2
id: robust-basic-sdp-gaps-from-gaussian-pair-sum-universe
kind: route
title: Fix n from the d-uniform value bound of the Gaussian pair-sum universe, then d from eta, then discretise the noncompact universe on a compact good set of well-conditioned matrices with one outer cell
target: rich-2to1-perfect-completeness-has-robust-basic-sdp-gaps
requires: [gaussian-pair-sum-universe-rich-2to1-game-has-vanishing-value]
artifacts:
  - experiments/gaussian-pair-sum-universe-2026-09-17/check_gaussian_universe.py
---

Unlike `robust-basic-sdp-gaps-from-rotated-frame-universe`, which needs the
OPEN vanishing value of the Haar-frame universe (an exactly perfect SDP
solution), this route uses a universe whose SDP solution is only
asymptotically perfect but whose value is proved to vanish uniformly in the
extra parameter `d`.

## Quantifiers

Given `delta > 0`, the value bound of the premise is independent of `d` and
tends to `0`, so fix `n` with `val(W_(n,d)) <= delta/2` for all `d`. Given
`eta > 0`, with `eta <= delta/2` without loss, use the SDP item of the premise
to fix `d >= 2n` with `Obj_(n,d) >= 1 - eta/2`. Put `eps = eta/20`. It remains to
discretise `W = W_(n,d)` at this `(n, d)`.

## Discretisation

**Step 1 (good sets).** For `R > 1` let `K_R` be the set of `2n x d` matrices
with `||X||_op <= R` and least singular value `>= 1/R`, and `K'_R` the same for
`n x d` matrices. Both are compact, and `X` and `Y` lie in them for some `R`
a.s. (full row rank, as `d >= 2n`). Fix `R` with `Pr[X notin K_R] <= eps` and
`Pr[Y notin K'_R] <= eps`. The polar map `U` is continuous on each good set,
hence uniformly continuous there.

**Step 2 (cells).** Partition `K_R` into finitely many Borel cells so small that
`U` varies by at most `eps` in maximum row distance on each cell, and add the
outer cell `R^(2n x d) \ K_R`. Do the same on the right. Each fine cell gets a
representative in the cell; each outer cell gets the representative `U = F`,
an arbitrary matrix with orthonormal rows.

**Step 3 (instance).** Left vertices are the left cells `c`, right vertices are
the right cells `e`. For each labelled 2-to-1 map `P` there is an edge
`(c, e, P)` with constraint `P(a) = b` and weight
`W(c, e, P) = Pr[X in C_c, Pi_P X in D_e, P]`. The instance is rich:
`Pr[P | X in C_c]` is uniform because `P` is independent of `X`.

**Step 4 (value).** A labelling of the cells lifts to the Borel strategy
`f o cell`, `g o cell` of `W`, with the same satisfied mass, since `W(., ., .)`
is the push-forward of the edge law. So `val <= val(W) <= delta/2`.

**Step 5 (SDP).** Use `z(c, a) = U(X_c)_a / sqrt(2n)` and
`z(e, b) = U(Y_e)_b / sqrt(n)`, with `U(X_c)` the representative's polar factor
(or `F` on the outer cell). Rows are orthonormal, so both GKOPTW Figure 1
constraints hold exactly (that SDP has no nonnegativity constraint). Compare
the per-edge objective with `F(X, P)` of the premise at a point `(X, Y, P)`
counted in `W(c, e, P)`:

* if both cells are fine, each of the `2n` inner products of unit vectors moves
  by at most `2 eps`, so the objective moves by at most
  `2n * 2 eps / (n sqrt2) = 2 sqrt2 eps`;
* otherwise both objectives lie in `[-sqrt2, sqrt2]`, so it moves by at most
  `2 sqrt2`, and this happens on mass at most `2 eps`.

So the basic SDP value is at least `Obj_(n,d) - 2 sqrt2 eps - 4 sqrt2 eps`.

**Step 6 (rational weights, if an unweighted instance is wanted).** As in Step 5
of `rotated-frame-universe-discretisation-proof`: round `Pr[X in C_c]` and each
conditional law of `e` given `(c, P)` to rationals with a common denominator,
keeping `Pr[P | c]` exactly uniform, so that the rounding moves at most `eps`
of total (l1) weight. The value moves by at most `eps` and the SDP objective,
bounded by `sqrt2` per edge, by at most `sqrt2 eps`. Duplicate edges by
multiplicity.

## Conclusion

Basic SDP `>= 1 - eta/2 - 7 sqrt2 eps >= 1 - eta/2 - 0.5 eta = 1 - eta`, and
`val <= delta/2 + eps <= delta`. The alphabets are `[2n], [n]` with `n`
depending on `delta` only. This is the target.

## Prerequisites that can fail separately

* The premise's value item: Theorem G (powering plus Nelson plus random-matching
  expansion) and the transfer of the reduction.
* The premise's SDP item: the Gram law of large numbers.
* The discretisation: compactness of the good sets and uniform continuity of
  the polar map on them.
