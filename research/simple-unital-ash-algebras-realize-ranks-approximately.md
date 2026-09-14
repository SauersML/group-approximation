---
rg: 2
id: simple-unital-ash-algebras-realize-ranks-approximately
kind: claim
title: Rank functions are uniformly dense in the continuous affine functions on the trace simplex of every simple unital ASH algebra
invalidates: [stw27-counterexample-via-ash-gluing-rank-gap]
distinct_from:
  ah-algebras-realize-ranks-approximately: that is the established homogeneous case, where trivial rank-one projections realize any profile; this is the recursive subhomogeneous case, where attaching maps force boundary values and the profile must be extended across each top cell.
  stw99-problem-xxiii-rank-problem: that asks for exact realization of every lower semicontinuous rank on every simple stably finite algebra; this asks only for uniform approximation of continuous ranks, on ASH algebras.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**OPEN.** Let `A` be a unital simple separable infinite-dimensional ASH
algebra, meaning an inductive limit of recursive subhomogeneous algebras over
finite-dimensional compact metrizable spaces, with no dimension-growth
hypothesis.  For every continuous strictly positive affine `f` on `T(A)` and
every `eta > 0` there is `y in M_infty(A)_+` with `|d_tau(y) - f(tau)| < eta`
for all `tau in T(A)`.

Payoff:

- Toms--Winter on the whole ASH class, through
  `ash-strict-comparison-z-stable-via-rank-density`.
- Every ASH candidate for the K1 route is excluded.

## Attempts

- **Reduction to one stage (sound, recorded here).**  By Brown--Perera--Toms
  Proposition 5.1 it suffices to show the following.  For a positive
  contraction `c` at some stage and every `delta > 0`, some later stage `R` and
  `b in M_infty(R)_+` satisfy

  ```text
  |rank b(x) - Tr c(x)| <= delta n(x)
  ```

  at every irreducible point `x` of `R`, where `n(x)` is the dimension at `x`
  and `c` has been pushed to `R`.  Extreme traces of a subhomogeneous algebra
  are the normalized irreducible traces.  A lower (resp. upper) semicontinuous
  affine function attains its minimum (resp. maximum) at an extreme point, so
  pointwise bounds give tracial bounds.
- **Homogeneous blocks.**  The Brown--Perera--Toms Lemma 5.2 construction
  works on the top cell with absolute defect 1.
- **The hinge is the attaching locus.**  On `X_k^(0)` the element is forced to
  be `sigma_k` of the lower-stage element.  It must be extended over `X_k` with
  rank within `delta n_k` of `Tr c`.
  - *Untwisted diagonal attaching maps.*  Every level has a diagonal model: a
    commutative coordinate algebra `C(Omega)`, with ranks equal to counts of
    coordinates in an open set.  The extension becomes a staggering problem:
    turn boundary coordinates off and designed coordinates on in a
    threshold-ordered way.  A proof with defect `O(1/N)` per level for minimal
    block size `N` is in progress, and level accumulation is not yet
    controlled.
  - *Twisted attaching maps.*  The support of the forced boundary element can
    be a nontrivial subbundle.  Extending it with rank drop at most `delta n_k`
    is obstructed by characteristic classes when `delta n_k` is below about
    half of `dim X_k`.  This is the Villadsen/LIX regime without slow
    dimension growth.
- **Slow dimension growth.**  With it, the twisted obstruction vanishes by
  stable range.  This is consistent with Winter's theorem (Invent. Math.
  2012, abstract) that slow dimension growth and Z-stability are equivalent
  for simple unital ASH algebras whose projections separate traces.
