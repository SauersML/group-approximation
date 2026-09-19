---
rg: 2
id: proposed-twisted-clifford-substitution-endomorphism-audit-proof
kind: route
title: Compute the triple-product square and separate it from the global HNN obligations
target: proposed-twisted-clifford-substitution-needs-endomorphism-audit
requires: []
artifacts:
  - experiments/renormalization_transport_audit.py
  - research/artifacts/renormalization-stable-letter-audit-2026-08-20.md
---

Moving the second copy of three pairwise anticommuting factors into matching
order takes three swaps, giving `(TCS2)`.  The replay script checks both
uniform square conventions.  The remaining assertions follow from the
definition of an ascending HNN extension: Britton's base-embedding conclusion
requires a well-defined injective base endomorphism, while a finite-window
operator calculation verifies neither preservation of all relators nor
compatibility with the acting tree group.

