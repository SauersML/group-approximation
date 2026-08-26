---
rg: 2
id: steinberg-standard-augmentation-filtration-firewall
kind: claim
title: Standard augmentation and PBW filtrations do not triangularize the Steinberg X row
artifacts:
  - research/steinberg-augmentation-pbw-firewall-proof.md
invalidates:
  - steinberg-x-dual-via-standard-augmentation-filtration
distinct_from:
  steinberg-x-plus-incidence-dual-is-surjective: this invalidates the standard associated-graded proof strategy, not the modular surjectivity statement itself.
---

**ESTABLISHED FIREWALL.**  For `k=F_p` and `G=SL_3(F_p)`, the global
augmentation ideal satisfies `I=I^2`, so its positive associated graded is
nonseparated and cannot lift the tempting congruence `X=-1 mod I` to the
Steinberg block.  The separated local Jennings/PBW filtration of a root
unipotent does not repair this: the outer coefficients `A^(-1),B^(-1)`
send the PBW bottom into every positive grade and the top back to grade
one.

This failure persists after quotienting by endpoint potentials.  For
`p>=5`, the zero-marginal class `[a^2c]` is sent by the `A` defect to a
normal form with nonzero coefficient `(1/4)[a^(p-2)c]`, while neither the
`B` defect nor `-1` can cancel that term.  Thus the actual quotient row
has a degree-three to degree-`p-1` jump.  Direct block Bezout and a new
two-sided filtration remain possible.

DERIVATION
steinberg-augmentation-pbw-firewall-proof
