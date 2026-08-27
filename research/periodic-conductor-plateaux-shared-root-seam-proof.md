---
rg: 2
id: periodic-conductor-plateaux-shared-root-seam-proof
kind: route
title: Count the bad clock columns and the unglued regular blocks
target: periodic-conductor-plateaux-pay-a-shared-root-seam
requires: []
---

For `(PCS1)`, direct inspection shows that conjugated successor agrees with
successor-by-two except at the two even/odd wrap columns.  Each bad column
contributes squared Euclidean norm `2`, so normalization by `L` gives
`(PCS2)`.  Telescoping powers yields `(PCS3)`.

Independent root clocks commute, whereas the third clock is a nontrivial
regular shift of trace zero.  Thus normalized trace expansion gives
`(PCS5)` exactly.

For `q_L=2^L-1`, the order argument following `(PCS6)` makes all local
diagonal scalings exact.  Distinct chamber factors contain distinct regular
group elements, whose left-regular unitaries have trace-orthogonal quotient;
hence every unglued literal root or internal-Weyl identity costs square `2`,
which is `(PCS8)`.

Finally decompose a block-diagonal model into glued mass `g` and separated
mass `1-g`.  The two overlaps are respectively `1/2` and `1/4`, proving
`(PCS9)`.  Every separated block contributes `2` to at least one seam, so
summing the six defects proves `(PCS10)` and the claimed `1/3` maximum floor.
