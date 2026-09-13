---
rg: 2
id: function-field-hecke-pair-is-relatively-embeddable
kind: claim
title: The function-field Hecke inclusion L(SL_3(F_2[t])) < L(SL_3(F_2[t,1/t])) is relatively embeddable over the scalars
distinct_from:
  function-field-hecke-pair-is-not-relatively-embeddable: that is the negative polarity of the same question; this is the positive polarity, which every Kun--Thom Q3.4 witness at the Bowen--Chapman parameters forces
  coset-wreath-is-hyperlinear: that asks about the arithmetic wreath over SL_3(Z) < SL_3(Z[1/3]); this is the function-field one-place Laurent pair
---

**OPEN.**  With `Lambda=SL_3(F_2[t,1/t])` and `C=SL_3(F_2[t])`, the inclusion
`L(C) subset L(Lambda)` is `RE/C`.  Equivalently, `Lambda *_C Lambda` is
hyperlinear.

The route from the Kun--Thom commutation stabilizer shows that this claim is
necessary for the Kun--Thom Q3.4 separation at `(q,r,d)=(2,3,3)`.

## Attempts

- **Sofic building action.**  Soficity of `Lambda action Lambda/C` (the
  type-zero building vertices) would suffice, by
  `sofic-coset-action-makes-amalgam-double-sofic`.  By
  `codense-kazhdan-coset-action-forces-permutation-outliers` and co-density
  (TR1), any sofic model would be noncorrectable to exact finite actions.  The
  number-field analogue is stuck at the same point
  (`sl3-dyadic-building-vertex-action-is-sofic`, whose rounding route needs
  coherent deck cocycles).
- **Opposite slice.**  `opposite-slice-contains-function-field-hecke-pair`
  sends every positive answer for the opposite Kun--Thom slice down to this
  pair.  No reverse transfer is known, so the slice is not an easier target.
