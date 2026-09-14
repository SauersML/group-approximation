---
rg: 2
id: subshift-el3-f2-iso-soe-from-all-q-statement
kind: route
title: The binary rigidity question is the q = 2 case of the rigidity statement over every finite field, since the binary groups are centreless
target: subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence
requires:
  - subshift-elementary-group-isomorphism-forces-orbit-equivalence
  - subshift-f2-ring-indicator-ideals-and-centreless-el3
---

Over `F_2` the centre of `EL_3(LC(X,F_2) ⋊ Z)` is trivial (`subshift-f2-ring-indicator-ideals-and-centreless-el3`), so
`EL_3(LC(X,F_2)⋊Z)/Z = G_X`. The case `q = 2` of `subshift-elementary-group-isomorphism-forces-orbit-equivalence` is
then exactly the target. ∎

Only the first requirement is open. This route makes the all-`q` statement reachable from the note's open-questions
root `simple-kazhdan-lef-groups-note-open-questions`.
