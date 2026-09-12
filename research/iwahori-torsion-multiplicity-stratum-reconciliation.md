---
rg: 2
id: iwahori-torsion-multiplicity-stratum-reconciliation
kind: claim
title: Supplied compatible endpoints permit exact small-rank torsion multiplicity reconciliation
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
  - research/artifacts/modular-multiplicity-rank-reconciliation-2026-09-08.md
  - research/artifacts/strict-iwahori-stratum-neighborhood-obstruction-2026-09-08.md
distinct_from:
  iwahori-newton-closes-near-sector: that asks for a nonlinear error bound after multiplicities are fixed and remains open; this moves a pair into a supplied compatible endpoint's stratum with dimension-uniform loss.
---

**Established qualitative reconciliation for a supplied endpoint.**
Suppose exact modular vertex pairs `pi,sigma` act in the same dimension
`d`, `sigma` is compatible, and their generator HS distance is `delta`.
There is an exact vertex pair `pi_hat` with the generator multiplicities
of `sigma`, at generatorwise normalized-rank distance at most `3delta^2`
from `pi` and HS distance at most `2sqrt(3)delta`. Every fixed Iwahori
residual changes by at most `C delta`. Thus as `delta->0` both the pair
movement and defect change are `o(1)`, with no padding.

The proof is `modular-multiplicities-reconcile-at-quadratic-rank-cost`.
It preserves the common central relation `S^2=B^3` by changing the
central sign on one shared small space, using separate finite cyclic
hulls for the two generators, before relabeling their remaining spectra.
The comparison pair `sigma` is left unchanged. This supplies one common
multiplicity stratum; it does not make the new pair compatible or justify
the separate Newton step.

Different torsion multiplicity strata are only
`O(d^(-1/2))` apart, so no dimension-independent metric tube isolates one
stratum. The exact common-central surgery is the additional ingredient
that makes the relabeling legitimate.

On the positive central sector the torsion spectra are `{+1,-1}` and
`{1,zeta_3,zeta_3^2}`; the full modular spectra are the fourth and
sixth roots of unity. Their fixed spectral gaps mean that changing
`r` eigenvalue labels costs
`Theta(sqrt(r/d))`. A stronger, still **OPEN**, defect-controlled version
says that either the
pair can be moved into a compatible stratum at cost `C def`, or the unmatched
spectral rank contributes at least `C^(-1)sqrt(r/d)` to the Iwahori defect.

## Attempts

- **The sharp boundary model is now explicit.**
  `sl2-half-explicit-strict-flexible-separation` deletes the single fixed
  line from the even Weil representation.  It has defect
  `Theta(d^(-1/2))`, is uniformly far from every exact same-dimensional
  representation by `(T;FD)`, and becomes exact after one dimension of
  flexible padding. It has no nearby compatible comparison in the
  original dimension, so it does not contradict the supplied-endpoint
  theorem above. The stronger defect-controlled target is
  `padding/d=O(defect^2)` (or its multi-block analogue).
- **The multi-block normalization is proved on the canonical boundary.**
  `direct-sum-weil-compressions-have-quadratic-padding` shows that `K`
  compressed even-Weil blocks in total dimension `D` have defect
  `O(sqrt(K/D))` and are repaired by exactly `K` restored lines.  Any general
  matching proof must treat this as low-density boundary mass, not as a
  packetwise positive gap.

- Continuous Newton cannot change the discrete multiplicities. The new
  surgery performs that discrete operation exactly at each vertex.
- The remaining construction is a compatible endpoint from a small defect,
  with the appropriate flexible dimension budget. Matching finite-order
  marginals alone does not construct one.

**Newton boundary.** The 2026-08-21 audit showed that
`iwahori-newton-closes-near-sector` cannot be invoked from the asserted
normalized-HS Taylor estimate: the rank-one direction that separates
strata (`O(d^(-1/2))` in normalized HS, `Theta(1)` in operator norm) is also
the direction on which the Newton step's second-derivative bound fails
(`normalized-hs-taylor-remainder-is-not-dimension-free`).  So the
within-stratum nonlinear bound is a separate problem after the qualitative
bookkeeping proved here. The new
`strict-iwahori-repair-has-no-uniform-hs-neighborhood` sharpens this
boundary: proximity to a supplied compatible point in the same stratum
does not give any dimension-uniform strict local repair modulus. Its
examples have bounded flexible repairs. The unrestricted nearest-point
stratum hypothesis in the older Newton formulation is not established
by that counterexample and is not silently being dropped.
