---
rg: 2
id: fanizza-native-additive-incidence-one-triangle-proof
kind: route
title: Enumerate the four native contexts and flatten their sole separator triangle
target: fanizza-native-additive-incidence-is-one-triangle
requires: []
---

The shared variables of `(FNI1)` are `O_Q` (three contexts) and `O_P`,
`Z_tilde` (two contexts each); the context-intersection graph has five
edges, including `C_X -- C_Z : O_Q`.  A running-intersection carrying graph
needs the two forced edges `C_D -- C_R`, `C_Z -- C_R` and a spanning tree of
the three `O_Q`-contexts, i.e. four edges on four vertices, so no join tree
exists and every minimal carrying graph is unicyclic.  The fixed choice
`(FNI2)` makes `C_X` a leaf and its unique cycle the triangle `(FNI3)`.

It is flat.  For every prescribed separator triple
`(O_Q,O_P,Z_tilde)`, satisfy `C_X,C_Z` by choosing the conditional comparison
signs equal when `O_Q=-1`, set `O_D` to the conjunction of `O_P,O_Q`, and in
`C_R` choose the last two signs of `(O_P,X_tilde O_P X_tilde,UO_PU*)` as
`(+,+)` for `O_P=+1` and `(+,-)` for `O_P=-1`.  This triple avoids the five
forbidden first-coordinate patterns, independently of the remaining signs.
Thus all eight separator assignments extend, proving both the one-triangle
description and its classical flatness.  The prescribed-word realization is
correctly left as the separate compiler hole.
