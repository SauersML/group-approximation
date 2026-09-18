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
* Structured label spaces fail (swarm-0917, 2026-09-17). Claim
  `pair-swap-groups-of-smooth-pairing-designs-contain-alt` shows that at
  every large `n`, an exactly 2-wise uniform law with
  `||1_E D_mu||_q <= C` has its kernel swaps generating a group that
  contains `A_(2n)`. So no witness preserves a subset, a partition, an
  affine or projective geometry, or a code on the labels. Subsets and
  partitions are ruled out by a degree-two moment identity together with a
  switching lemma. Primitive geometries are ruled out by Maroti's order
  bound set against the `m^n` entropy count. In the edge-transitive case
  the law must be uniform on all pairings, which is circular. The route
  `finite-moment-hardness-via-structured-label-groups` is dead. What
  survives is exponentially large laws whose swaps generate `Alt(2n)` and
  that are not one orbit of the vertex stabilizer.
* Projective alphabet lifts cannot amplify (swarm-0917, 2026-09-17).
  Split the hole into (a) a combinatorial amplification to `t`-wise uniform
  bounded-moment laws and (b) a soundness transfer. Part (a) alone is
  already met by standalone designs, so the difficulty sits entirely in (b).
  Claim `projective-alphabet-lifts-cannot-amplify-pairing-moments` kills
  the case where (b) is projective, meaning `p' o phi' = phi o p` for label
  maps `p` from an arbitrary hard instance.
  * **Transfer inequality.** For every map of weight `w` and surplus
    `g = 2n' - |p(Sigma')|`,
    `||1_(E') D'||_q >= w theta_* m^((q-2) g/(2q))`, and the output moment
    dominates the pulled-back input moment.
  * **Consequence.** A bounded surplus gives no amplification. An unbounded
    surplus blows up for `q >= 3` unless there are `exp(Omega(n'/log n'))`
    projections per vertex, even for polynomial-support inputs (support count
    `(2n')^(3g/2)` per input kernel).
  * **Evidence.** Exact regression checks are in
    `experiments/projective-amplification-2026-09-17/`. The doubling lift of
    the fully rich law reaches moment `2.27e14` at `n = 64`, while the uniform
    law stays below 1.8.
  * **Status.** The route `finite-moment-hardness-via-projective-amplification`
    is dead.
  * **What survives.** Non-projective transfers that pair across input kernel
    classes on a constant fraction of pairs (list decoding, BKM Appendix B
    merges), long-code re-encodings with exponentially many projections, and
    `q = 2`.
