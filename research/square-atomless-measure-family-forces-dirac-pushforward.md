---
rg: 2
id: square-atomless-measure-family-forces-dirac-pushforward
kind: claim
title: Some compact family of atomless measures on the square makes every continuous function push some member to a Dirac measure
distinct_from:
  zero-dimensional-atomless-diagonal-divides-unit: that uses an injective function on a zero-dimensional diagonal to produce a self-adjoint element with atomless spectral distributions; this shows that from dimension 2 no function on the diagonal survives every compact atomless family, so that argument does not extend.
  bauer-strict-comparison-unit-divides-iff-atomless-element: that characterizes division by elements with small atoms; this is a commutative model in which small atoms are unavailable, forced by Lebesgue's covering theorem rather than by characteristic classes.
artifacts:
  - research/artifacts/ex2-tw-square-dirac-pushforward-2026-09-13.md
---

**Proposition.** Let `S = [0,1]²`. There is a weak*-compact set `𝓜` of atomless
probability measures on `S` such that every continuous `f: S → ℝ` has some `μ ∈ 𝓜` for
which `f_*μ` is a Dirac measure.

Take `𝓜` to be the measures whose first or second coordinate marginal is normalized
Lebesgue measure on some interval of length at least `1/√2`.

**Proof** (route `square-atomless-measure-family-forces-dirac-pushforward-proof`).
- **A large component.** Factor `f` through the space of components of its level sets, which
  has dimension at most 1 by Hurewicz's formula. If every component had diameter `< 1`, a
  pulled-back cover of order 2 would contradict Lebesgue's covering theorem. So some
  component `C ⊆ f^{−1}(c)` has diameter at least 1.
- **The measure.** One coordinate projection of `C` is an interval `J` of length at least
  `1/√2`. A Borel selection over `J` carries `Leb_J` to a member of `𝓜` supported on `C`.

**Meaning.**
- **Commutative rigidity.** Suppose the extreme traces of an algebra restricted to a diagonal
  `C(S)` formed `𝓜`. Then no element of the diagonal could supply condition (ii) of
  `bauer-strict-comparison-unit-divides-iff-atomless-element`, whereas zero-dimensional
  diagonals always do.
- **Dimension theory, not cohomology.** This forcing comes from Lebesgue's covering theorem,
  like the staircase charges. The Pauli tower's forcing comes from a top Stiefel–Whitney class.

**Not claimed.** No strict-comparison algebra realizing `𝓜` on a diagonal was built.

Unreviewed.
