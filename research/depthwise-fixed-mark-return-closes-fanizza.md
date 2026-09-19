---
rg: 2
id: depthwise-fixed-mark-return-closes-fanizza
kind: route
title: Take the canonical microstate limit before the Fanizza heat-depth limit
target: fanizza-canonical-profile-groupification
requires:
  - fanizza-depthwise-fixed-mark-return
  - fanizza-fixed-heat-depth-survives-hs-microstates
  - group-algebra-mark-reverse-kleene-collapse
---

HALT completeness is clause 1 of the return claim.  On a NONHALT canonical
microstate sequence, fix `t`; the finite relator and trace-window errors in
`(DFR1)` vanish, while `(FHM2)` bounds the amplitude by `C_m/(4t^2)`.  This
gives `(DFR2)`.  Now send `t` to infinity.  The fixed group-algebra mark
collapses on every canonical-profile sequence, exactly as required by
`fanizza-canonical-profile-groupification`; reverse Kleene accepts this mark.
