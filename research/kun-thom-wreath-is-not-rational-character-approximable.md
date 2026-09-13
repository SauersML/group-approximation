---
rg: 2
id: kun-thom-wreath-is-not-rational-character-approximable
kind: claim
title: The Kun--Thom coset wreath admits no rational-character finite-group approximation, so that route to the determinant conjecture stops at it
invalidates: [determinant-conjecture-via-rational-character-models]
distinct_from:
  hilbert-embeddable-witness-impossible: that excludes every approximation of the wreath by finite subgroups of unitary groups in normalized Hilbert--Schmidt; this records the consequence for the rational-character mechanism that proves the determinant conjecture
  determinant-violation-needs-nonsofic-support-subgroup: that localizes any violation to a nonsofic support; this shows that one integral approximation scheme beyond permutations already fails on a known nonsofic group
---

**ESTABLISHED** by `kun-thom-wreath-not-rational-character-approximable-proof`.

Let `W = (directSum_(G/Gamma) Z/2) semidirect G` be the Kun--Thom wreath of
`hilbert-embeddable-witness-impossible`. Then `W` is not rational-character
approximable in the sense of
`rational-character-approximable-groups-obey-determinant`.

**Consequence.** The determinant conjecture for `W`, if true, needs integrality
from outside finite-group models: for instance one-variable integer
approximation of each spectrum (`integral-group-ring-spectra-are-integer-root-limits`),
or a mechanism with no approximation at all. The route
`determinant-conjecture-via-rational-character-models` is dead.

Trust surface: inherited from Kun--Thom arXiv:2608.06222, Theorem 4.1, through
`two-point-approximation-fails`.
