---
rg: 2
id: property-t-free-existence-via-jacobson-two-braid-gap
kind: route
title: Use the explicit three-ray mark and a positive two-braid matrix gap
target: nonhyperlinear-property-t-free-explicit-mf-witness
requires:
  - jacobson-joint-cells-are-two-braids
  - jacobson-two-braid-gap-characterizes-mark-collapse
  - jacobson-two-braid-mixed-packet-gap
---

Take the explicit finitely presented joint group `Gamma` and nontrivial
head mark `w` in the first prerequisite. A positive value of the
infimum in the third prerequisite makes every norm-corona homomorphism
kill `w`, by the second prerequisite. Thus `Gamma` would be non-MF.
**Invalidated:** `jacobson-two-braid-infimum-is-zero` disproves the
positivity prerequisite by constructing a marked amenable quotient.
This particular presentation and head mark cannot establish the requested
non-MF existence theorem. The independent existence goal remains open.
