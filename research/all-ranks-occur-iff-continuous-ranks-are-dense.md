---
rg: 2
id: all-ranks-occur-iff-continuous-ranks-are-dense
kind: claim
title: All ranks occur exactly when the rank functions that are continuous on the quasitrace simplex are uniformly dense
distinct_from:
  ah-algebras-realize-ranks-approximately: that is rank density, uniform approximation of continuous affine functions by arbitrary and typically discontinuous rank functions; this shows that approximation by continuous rank functions is already equivalent to exact realization of every rank.
  rank-density-from-approximate-rank-division: that reduces rank density to approximate integer division of ranks; this is the separate passage from approximate to exact realization, which rank density does not supply.
---

Let `A` be a unital simple separable C*-algebra with `QT(A)` nonempty. For
`a in (A tensor K)_+` write `d(a)` for the lower semicontinuous affine function
`tau -> d_tau(a)` on `QT(A)`. Call `d(a)` a *continuous rank* when it is finite
and continuous on `QT(A)`. The following are equivalent.

1. All ranks occur (STW Problem XXIII holds for `A`): every lower
   semicontinuous affine `f: QT(A) -> (0, infinity]` equals `d(a)` for some
   positive `a in A tensor K`.
2. Every strictly positive continuous affine function on `QT(A)` is a rank.
3. Continuous ranks are uniformly dense in the strictly positive continuous
   affine functions: for every such `f` and every `eta > 0` there is
   `a in (A tensor K)_+` with `d(a)` continuous and `|d(a) - f| < eta` on
   `QT(A)`.

No stable rank, comparison, nuclearity or boundary hypothesis enters.

**Why rank density is not enough.** Rank density (RD) gives the uniform
approximation in item 3 by ranks that need not be continuous. Subtracting a
discontinuous rank from a continuous target leaves an upper semicontinuous
residual. A lower semicontinuous rank below an upper semicontinuous function
can miss it by a fixed amount at every point of a closed set with empty
interior. So the greedy upgrade breaks at the first step. Continuity of the
approximants is exactly what repairs it.

**Relation to Lin's oscillation.** Lin's tracial oscillation
`omega(a) = lim_n sup_tau (d_tau(a) - tau(f_(1/n)(a)))` vanishes exactly when
`d(a)` is continuous (H. Lin, arXiv:2112.12036, §5 definition of `omega`). So
item 3 says that zero-oscillation elements have uniformly dense ranks.
Fu--Lin (arXiv:2112.14007, Theorem `Teqiv`) prove that tracial approximate
oscillation zero, the 2-norm density of such elements, is equivalent to
surjectivity of the rank map plus stable rank one. They assume strict comparison
throughout. The equivalence here assumes no comparison and uses uniform density
of ranks, not 2-norm density of elements.

**A second use.** If `d(a) + d(b)` is continuous and both are finite, then
`d(a) = (d(a) + d(b)) - d(b)` is both lower and upper semicontinuous. So every
orthogonal summand of an element with continuous rank has continuous rank.
This is what makes item 3 testable on a concrete algebra: see
`doubling-ah-finite-stage-continuous-ranks-are-constant`.
