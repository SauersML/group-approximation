---
rg: 2
id: non-ce-bcs-positive-one3-reduction-proof
kind: route
title: Specialize the moment-exact fixed-language reduction to positive ONE3
target: non-ce-bcs-has-positive-one3-weighted-form
requires:
  - mipstar-bcs-tracial-nonru-exists
  - culf-mastel-global-moment-exact-rounding
  - pointed-weighted-defect-gap-pulls-back
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
---

Positive ONE3 is a fixed Boolean NP-complete language, so the Culf--Mastel
Boolean fixed-language construction applies.  Exact classical extensions
and subdivisions carry the source tracial solution forward.  Lemma 3.10
rebuilds only the context measurements and proves the stated moment and CE
preservation.  The reverse weighted maps pull any perfect CE target trace
back to the forbidden source trace.  Finally apply the pointed defect
inequality through the finite chain of constants.  This gives `(N13-1)` and
its quantitative strengthening.

