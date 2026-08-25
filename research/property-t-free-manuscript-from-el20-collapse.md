---
rg: 2
id: property-t-free-manuscript-from-el20-collapse
kind: route
title: Derive the retained manuscript endpoints from direct EL20 collapse
target: property-t-free-manuscript-results
requires:
  - property-t-free-el20-full-mf-radical
  - property-t-free-el20-collapse-transfers-to-el12
  - property-t-free-manuscript-theorem-dependency-audit
---

Transfer the direct elementary-group collapse from rank twenty to the
manuscript's literal `EL_12(R)` by the explicit binary-prefix equivalence.
The theorem dependency audit then supplies every retained non-Kazhdan
endpoint: radical and closure calculus, simplicity and defect statements,
full-kernel pullback and factorization, the prescribed-quotient construction,
and the non-MF consequences.  This route bypasses the Steinberg central
kernel completely.  The final Lean import cone must still use the audited
algebra-only rank equivalence and endpoint modules rather than files which
also expose Property `(T)` declarations.

