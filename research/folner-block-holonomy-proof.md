---
rg: 2
id: folner-block-holonomy-proof
kind: route
title: Count the one-step wrap and the four-step interior returns blockwise
target: folner-block-shifts-do-not-dilute-four-matcher-holonomy
requires: []
---

The direct sum in `(FBS2)` is exact blockwise.  Away from the one cyclic
wrap, the matcher difference in `(FBS3)` is a conjugate of
`D-SPS^*`, so its squared normalized-HS contribution is `epsilon^2`.
The remaining block contributes at most `4`; normalized block averaging
gives `(FBS3)`.

For the fourth power, each of the `L-4` interior blocks is a conjugate of
`S^4PS^(-4)-P`, hence contributes exactly `h^2`.  Each of the four wrapping
blocks contributes between zero and four.  Averaging proves both bounds in
`(FBS4)`.  The varying-gauge statement is the same calculation with the
ordered four-increment product in place of `S^4`.

