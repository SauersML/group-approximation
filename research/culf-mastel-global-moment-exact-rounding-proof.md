---
rg: 2
id: culf-mastel-global-moment-exact-rounding-proof
kind: route
title: Read the unchanged global operators in the Lemma 3.10 construction
target: culf-mastel-global-moment-exact-rounding
requires:
  - pointed-weighted-defect-gap-pulls-back
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
---

Culf--Mastel construct `chi` inside the original tracial von Neumann algebra
and define it by `(GMR1)` on every global generator.  Evaluation of a star
polynomial commutes with this literal identification, proving `(GMR2)`.
Their Lemma 3.10 estimate gives `(GMR3)`.  Because no ambient algebra is
enlarged, a CE embedding of the input algebra also embeds the output
operators.  Applying the pointed-gap proof trace by trace gives the last
assertion even though `chi` depends on the input trace.

