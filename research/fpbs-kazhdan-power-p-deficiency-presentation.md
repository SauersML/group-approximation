---
rg: 2
id: fpbs-kazhdan-power-p-deficiency-presentation
kind: claim
title: Some Kazhdan group has a presentation of positive power p-deficiency
refuted_by:
  - fpbs-power-p-deficiency-excludes-property-t
distinct_from:
  fpbs-power-p-deficiency-excludes-property-t: that is the established theorem refuting this claim; this is the candidate hypothesis it refutes.
  fpbs-kazhdan-positive-rank-gradient: that is the open Farber-chain target; this was a sufficient hypothesis for it and is now refuted.
---

**REFUTED.** Some group with property (T) has a presentation `(X,R)`, `X`
finite, with `|X| - 1 - sum_(r in R) p^(-nu_p(r)) > 0` for some prime `p`.

This is recorded as a candidate premise because it would have produced the
Kazhdan certificate (`fpbs-kazhdan-gradient-via-power-p-deficiency`). It is
false by `fpbs-power-p-deficiency-excludes-property-t`.

## Attempts

* **Add Kazhdan relators to a positive power-deficiency presentation.** For
  example, quotient a Schlage-Puchta-type torsion presentation by the finitely
  many relators of a finitely presented Kazhdan group. **Dead:** after the
  Kazhdan relators are added, openness of (T) gives a finitely presented
  truncation that is both Kazhdan and of positive power `p`-deficiency.
  Lackenby makes it `p`-large, a contradiction. The same argument kills every
  presentation, not only this shape.
