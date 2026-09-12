---
rg: 2
id: surjunctive-groups-are-quantitatively-surjunctive
kind: claim
title: Every surjunctive group has a uniform entropy-type deficit for injective maps into powers of proper subshifts
distinct_from:
  gottschalk-surjunctivity-conjecture: that concerns injective automata between equal full shifts; this asks, on a group already known to be surjunctive, for a deficit linear in the number of copies of a proper subshift, which the conjecture does not obviously give.
  injective-ca-images-have-full-single-site-entropy: that is a single-site entropy bound for images of the full shift over one alphabet; this compares injective maps into products of copies of a proper subshift with a free full-shift track.
artifacts:
  - research/artifacts/product-fibre-garden-of-eden-filter-2026-09-12.md
---

**OPEN.** Call `G` *quantitatively surjunctive* if the following holds for every finite alphabet `B`
and every proper subshift `Y` of `B^G`. There is `delta_Y > 0` such that for every finite alphabet `D`
and all `n >= 1`, `j, j' >= 0` with `(j' - j) log|D| < delta_Y n`, no injective cellular automaton maps
`(B^n x D^j)^G` into `Y^n x (D^(j'))^G`. The claim is that every surjunctive group has this property.

**What is known** (Section 3 of the artifact):
- a quantitatively surjunctive group is surjunctive (take `n = 1`, `j = j' = 0`);
- sofic groups are quantitatively surjunctive, with
  `delta_Y = -log(1 - |B|^(-|W|)) / (|W|^2 + 1)` for a pattern `r` on `W` missing from `Y`;
- if `G` is quantitatively surjunctive and `K` is sofic, then `G x K` is surjunctive.

## Attempts

- **Counting on sofic models (w4-free-pos-b).** It proves the sofic case.
  - **Lower bound.** Outputs determine inputs at good points.
  - **Upper bound.** Each track misses the pattern on a positive fraction of disjoint windows.
  - **Where it stops.** Both bounds need finite models of `G`.
- **Known surjunctive nonsofic groups.** They lie in the LEF permanence closure. Whether its operations
  preserve the property is not recorded. A proof along the finitary split-extension peeling would have
  to carry the deficit through each peeled stratum. That has not been attempted.
