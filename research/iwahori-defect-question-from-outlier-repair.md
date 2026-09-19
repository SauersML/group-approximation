---
rg: 2
id: iwahori-defect-question-from-outlier-repair
kind: route
title: Full-rank outlier repair answers the local-to-global defect question
target: iwahori-local-global-defect-question
requires:
  - iwahori-outlier-repair
artifacts:
  - notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md
  - notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
---

This is a reduction, not a restatement, and the difference is the sector
analysis.

`iwahori-local-global-defect-question` asks for a modulus `f` with
`D(π) ≤ f(def(π))` over the *whole* representation variety
`X_FD(SL₂(ℤ) * SL₂(ℤ))`. The HIGHEST_YIELD analysis (2026-08-14) decomposes
that variety into sectors by the behaviour of the mixed edge representation and
disposes of all but one: the matched central-regular sector, where the
low-energy operator space carrying the almost-invariant identity is `o(d_n²)`
and one needs to extract from it an exact invertible edge intertwiner after
`o(d_n)` padding. `iwahori-outlier-repair` is exactly that extraction.

So the prerequisite is strictly weaker than the target in two respects that can
independently fail: it is confined to one sector, and it asks only for an
intertwiner after bounded-density padding rather than for a uniform modulus.
What converts it back to the target is the sector decomposition, which is this
repository's own work and is recorded in the notes cited above, not in
Dogon–Vigdorovich.

Consequently a *negative* answer to the question does not refute
`iwahori-outlier-repair`, and a refutation of the repair theorem in its sector
would leave the question open only if the sector decomposition were wrong.
Anyone weakening the repair statement must re-check that the decomposition
still covers the complement.
