---
rg: 2
id: lin-cross-gram-iwahori-scope-proof
kind: route
title: Compose the cross-Gram cutoff with Selberg and audit the side and rank of Lin's dilation
target: lin-cross-gram-localizes-authenticated-iwahori-overlap
requires:
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
  - lin-state-dependent-gh-preserves-the-commutant
  - lin-state-local-gh-is-an-intertwining-exactifier
  - lin-canonical-dilation-twirls-unprotected-left-carriers
  - long-bs14-packets-defeat-invariant-op-thresholding
  - cuspidal-redistribution-refutes-regular-core-orbit-basin
---

The first required claim gives the selected corner and its same-dimensional
Selberg exactification under an authenticated commutant gap. The next two
give exact opposite-algebra intertwining and the uncompressed state-local
intertwining identity, while the following claim computes the Reynolds
action on every unprotected left operator. Those formulas
prove both the positive localized composition and the left-side firewall.

The example `T=1` with arbitrary `R` verifies directly that `(GOI2)` does
not supply a finite-group representation.  Lin's stated target space is the
packet-size amplification and its estimate is in the chosen density norm,
so neither a global normalized-HS estimate nor energy-proportional padding
follows.  Finally the fourth required claim is an exact moving-level family
where an apparently small active spectral cut has full exact BS hull.  This
proves that approximate source reduction cannot replace the missing
authentication step.  Together these observations establish the stated
conditional advance and the first four scope limitations.

For the fifth, the cuspidal-redistribution claim keeps every noncuspidal
regular multiplicity and changes a positive-density cuspidal sector.  The
common noncuspidal part has limiting density `1/2`; the one cuspidal type
present on both sides contributes only `O(1/p)`.  Hence the largest genuine
common subrepresentation has density `1/2+o(1)`.  Both endpoints are exact,
so the unmatched half has zero defect and cannot be discarded or charged.
This proves that positive-overlap localization is only a peeling theorem,
not adaptive endpoint-type authentication.
