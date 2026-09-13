---
rg: 2
id: finite-moment-pairing-2to1-hardness
kind: claim
title: Near-perfect versus near-zero 2-to-1 hardness exists on designs with a bounded finite pull-back density moment
distinct_from:
  smooth-design-rich-2to1-hardness: that requires pointwise domination on every balanced coloring; this requires only one fixed finite Lq density moment at a time.
artifacts:
  - research/artifacts/unique-games-finite-density-moments-2026-09-12.md
---

For every `m>=2`, `K>=1`, and integer `q>=2`, there exists a constant
`C=C(m,K,q)>=1` such that for every `0<eta<1/2`, integer `t>=1`, and `n0`,
at some `n>=max(n0,t)`, `Gap-2-to-1_n[1-eta,eta]` is NP-hard on regular
instances satisfying the following at every left vertex. Its edge-induced
law `mu` on pairings of `[2n]` is exactly `t`-wise uniform, and

```
||1_(E_(K,m,n)) dnu_(mu,m)/dU_(2n)||_q <= C.
```

The set `E_(K,m,n)` is the BKM roughly balanced set. The pull-back law
`nu_(mu,m)` colors the pairs independently and uniformly from `[m]`.
The constant is independent of `eta,t,n`; each instance need only obey
the chosen `m,K,q`. NP-hardness and polynomial encoding are part of this
open claim, not consequences of the existence of standalone distributions.

By artifact equation (2), the density condition is exactly an average
balanced component-coloring bound for the union of `q` independent
edge-induced matchings. It still requires exponentially many support
matchings by equation (3). No outer construction satisfying it is known
in this repository.

## Attempts

* Existing smooth-design distributions satisfy the finite-moment bound
  by pointwise domination, and `finite-moment-hardness-from-smooth-design`
  proves the conditional hardness implication. Standalone distributions
  carry no PCP constraints or soundness theorem, so their existence does
  not establish this claim.
* The overlap identity in artifact Section 3 replaces a separate bound
  for every balanced coloring by an average component-coloring count
  for `q` sampled matchings. The exact replay checks that identity on
  bounded examples. No estimate for an NP-hard family is supplied;
  rare overlapping matching tuples must still be controlled.
* Subexponential pairing support still fails: artifact Section 4 gives
  `|supp(mu)| >= (theta/C)^(q/(q-1)) m^n`, where `theta` is the fixed
  positive balanced pull-back mass. Finite moments remove the pointwise
  certificate requirement but do not remove this entropy obstruction.
* The live missing step is an outer hardness construction with exact
  design strength `t` and a bound `C(m,K,q)` independent of both `t`
  and the source error. The noise tail theorem fixes the later analytic
  cutoff and does not manufacture such a construction.
