---
rg: 2
id: agent-free-compressor-full-localization-implies-kernel-sector
kind: route
title: Forget the finite packet action after localized quotient factorization
target: agent-free-compressor-payload-kernel-fixed-sector
requires:
  - shared-bcs-carrier-localizes-free-compressor-quotient
---

Take the positive-density adjoint projection supplied by full carrier
localization.  Factorization of the parent `F` action through `theta:F->B_f`
gives `(PKF2)` for the finite normal generators, while reduction by the
parent action gives `(PKF3)`.  The lower bound in clause 1 of full
localization is exactly `(PKF1)`.  Discard the decoded child action and the
moved-parent-generator clause: the infinite kernel is already terminal by
`agent-free-compressor-kernel-carrier-is-terminal`.

