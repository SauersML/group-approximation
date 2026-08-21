---
rg: 2
id: iwahori-torsion-multiplicity-stratum-reconciliation
kind: claim
title: Small-rank torsion multiplicity changes can be reconciled before the Iwahori Newton step
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  iwahori-newton-closes-near-sector: that gives the nonlinear error bound after multiplicities are fixed; this must move a nearby pair and compatible point into one common stratum with dimension-uniform loss.
---

OPEN. Suppose a pair of exact modular representations is close in normalized
Hilbert--Schmidt norm to a compatible pair, but their order-two/order-three
spectral multiplicities differ on `o(d)` dimensions.  Prove that one may
reconcile those multiplicities, in the same dimension or with explicitly
controlled flexible padding, while changing the pair and its Iwahori defect
by `o(1)`.  The resulting pair and compatible comparison point must lie in
one common multiplicity stratum, where
`iwahori-newton-closes-near-sector` applies.

This is not formal: different torsion multiplicity strata are only
`O(d^(-1/2))` apart, so no dimension-independent metric tube isolates one
stratum.  The repair must use the two vertex restrictions and not merely
round the finite-order generators independently.

Because the torsion spectra are the fixed sets `{+1,-1}` and
`{1,zeta_3,zeta_3^2}`, changing `r` dimensions costs
`Theta(sqrt(r/d))`. A sufficient quantitative version says that either the
pair can be moved into a compatible stratum at cost `C def`, or the unmatched
spectral rank contributes at least `C^(-1)sqrt(r/d)` to the Iwahori defect.

## Attempts

- **The sharp boundary model is now explicit.**
  `sl2-half-explicit-strict-flexible-separation` deletes the single fixed
  line from the even Weil representation.  It has defect
  `Theta(d^(-1/2))`, is uniformly far from every exact same-dimensional
  representation by `(T;FD)`, and becomes exact after one dimension of
  flexible padding.  Thus no same-dimensional stratum theorem is possible;
  the correct quantitative target is precisely
  `padding/d=O(defect^2)` (or its multi-block analogue).
- **The multi-block normalization is proved on the canonical boundary.**
  `direct-sum-weil-compressions-have-quadratic-padding` shows that `K`
  compressed even-Weil blocks in total dimension `D` have defect
  `O(sqrt(K/D))` and are repaired by exactly `K` restored lines.  Any general
  matching proof must treat this as low-density boundary mass, not as a
  packetwise positive gap.

- Continuous Newton cannot change the discrete multiplicities.
- Discarding the changed block works only for flexible stability; the native
  endpoint requires an explicitly controlled same-dimensional repair.
- The live attack is a finite min-cost matching problem for the six spectral
  projections of the two torsion generators. Fixed spectral separation pays
  the correct square-root-rank scale. The unresolved step is realizing a
  matched overlap table by one common compatible block, rather than merely
  matching its row and column marginals.
