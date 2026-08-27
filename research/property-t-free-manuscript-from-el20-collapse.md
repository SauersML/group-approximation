---
rg: 2
id: property-t-free-manuscript-from-el20-collapse
kind: route
title: Derive the retained manuscript endpoints from the EL20 and torsion-free collapses
target: property-t-free-manuscript-results
requires:
  - property-t-free-el20-full-mf-radical
  - property-t-free-torsion-free-full-mf-radical
  - property-t-free-el20-collapse-transfers-to-el12
  - property-t-free-manuscript-theorem-dependency-audit
---

Transfer the direct elementary-group collapse from rank twenty to the
manuscript's literal `EL_12(R)` by the explicit binary-prefix equivalence.
The independent torsion-free input supplies the second main theorem with its
Property-`(T)` clause deleted.  The theorem dependency audit then supplies
every retained no-`(T)` endpoint.  This route bypasses the Steinberg central
kernel completely.  The final Lean import cone must use the audited
algebra-only modules rather than files which expose Property `(T)`
declarations.
