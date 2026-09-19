---
rg: 2
id: arbitrary-selector-normalizer-wordizes-stabilizer-corrector
kind: route
title: Use an arbitrary selector-group normalizer to wordize every stabilizer corrector
target: tailored-checks-to-common-marked-group-extensions
requires:
  - stabilizer-corrector-hermitianizes-zero-compression
---

**INVALIDATED UNIVERSAL-NORMALIZER PROPOSAL.**  Suppose the selected
character idempotent `q` belongs to a finite selector packet and a payload
word `w` has `q w q=0`.  Adjoin one stable letter `s` which normalizes the
selector group, fixes the selected character, and obeys `(sw)^2=1`.  Claim
that some permitted selector automorphism can always be assigned to `s`, so
the operator-level stabilizer corrector is wordized without imposing full
packet centralization.

`selector-normalizer-corrector-has-an-atom-permutation-criterion` invalidates
this universal claim.  The atom permutation `sigma` of the payload must
admit a permitted selector automorphism `alpha`, fixing the selected atom,
for which `(alpha sigma)^2=1`.  The regular four-character packet of `C_4`
and the payload permutation `(0 1 2)` have no such `alpha`: the only packet
automorphisms are the identity and `j |-> -j`, producing respectively a
three-cycle and a four-cycle.  The unrestricted selected-projection
corrector still exists.
