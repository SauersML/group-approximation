---
rg: 2
id: fanizza-native-additive-incidence-one-triangle-proof
kind: route
title: Enumerate the four native contexts and flatten their sole separator triangle
target: fanizza-native-additive-incidence-is-one-triangle
requires: []
---

The context list `(FNI1)` has exactly the four shared-variable edges in
`(FNI2)`.  The `C_X` vertex is a leaf; the remaining three edges form the
triangle `(FNI3)`, and deleting any one gives a join tree.  Connectedness for
the three shared variables forces all three edges, so this is the unique
running-intersection obstruction.

It is flat.  For every prescribed separator triple
`(O_Q,O_P,Z_tilde)`, satisfy `C_X,C_Z` by choosing the conditional comparison
signs equal when `O_Q=-1`, set `O_D` to the conjunction of `O_P,O_Q`, and in
`C_R` choose the last two signs of `(O_P,X_tilde O_P X_tilde,UO_PU*)` as
`(+,+)` for `O_P=+1` and `(+,-)` for `O_P=-1`.  This triple avoids the five
forbidden first-coordinate patterns, independently of the remaining signs.
Thus all eight separator assignments extend, proving both the one-triangle
description and its classical flatness.  The prescribed-word realization is
correctly left as the separate compiler hole.
