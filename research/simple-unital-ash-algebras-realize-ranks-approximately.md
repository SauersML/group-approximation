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
    coordinates in an open set.  The extension over a collar (CW pairs,
    neighborhood retractions) becomes a staggering problem: boundary
    coordinates switch off and designed coordinates switch on at
    coordinate-dependent times.
    - With a matrix amplification `M_L` whose digits are reserved one per
      level, switching times are exactly equidistributed and the count
      interpolates with error `O(1/L)` per level.  But this realizes only
      `L` times the profile.  That is free in any algebra
      (`rank-density-from-approximate-rank-division`), so it does not bear on
      the problem.
    - Without amplification, the switching labels must be equidistributed
      inside every inherited on-set of each block.  Those on-sets are
      decision lists over the chain of levels, and Halton-type labels give
      per-block discrepancy about `(log N)^(2l)/N` with `l` levels and minimal
      block size `N`, plus additive accumulation over levels.  So the argument
      closes only under a growth condition relating the number of RSH levels
      to block sizes along the tower.  It is not unconditional.
- **Reduction to division (established).**
  `rank-density-from-approximate-rank-division` shows rank density needs only
  approximate integer division of rank functions.  For ASH algebras the
  question is whether large-multiplicity connecting maps and the attaching
  maps admit continuous `1/L` sub-selections of summands up to small tracial
  error.  This is the ASH form of the soft-divider hinge recorded on STW
  XXVII.
  - *Twisted attaching maps.*  The support of the forced boundary element can
    be a nontrivial subbundle.  Extending it with rank drop at most `delta n_k`
    is obstructed by characteristic classes when `delta n_k` is below about
    half of `dim X_k`.  This is the Villadsen/LIX regime without slow
    dimension growth.
- **Slow dimension growth.**  With it, the twisted obstruction vanishes by
  stable range.  This is consistent with Winter's theorem (Invent. Math.
  2012, abstract) that slow dimension growth and Z-stability are equivalent
  for simple unital ASH algebras whose projections separate traces.
