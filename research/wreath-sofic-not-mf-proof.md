---
rg: 2
id: wreath-sofic-not-mf-proof
kind: route
title: The two halves conjoin at the literal sign-free quotient
target: wreath-sofic-not-mf
requires:
  - sign-free-quotient-sofic
  - commuting-lamp-quotient-not-mf
artifacts:
  - GroupApproximation/Sofic/CommutingLampQuotientSofic.lean
---

## Why sufficient

Both halves are established at the same literal group, the sign-free
quotient of the Kazhdan--Clifford witness: soficity by the mod-two
identification and the telescope-window pipeline
([[sign-free-quotient-sofic]]), non-MF-ness by the commuting-lamp
collapse ([[commuting-lamp-quotient-not-mf]]).  The conjunction is
packaged as one kernel-checked declaration,
`literalSignFreeQuotient_isSofic_and_not_isCDEOperatorMF`, and finite
generation is inherited from the witness group through the quotient
map.  This separates soficity from matricial-field approximability on
an explicit finitely generated group.
