---
rg: 2
id: quotient-benign-witness-gives-rope-synchronization
kind: route
title: Enhance the positive benign witness and apply the finite swap quotient
target: positive-rope-profinite-edge-synchronization
requires:
  - quotient-benign-rope-synchronizes-finite-quotients
  - positive-scaffold-has-quotient-compatible-rf-witness
---

Use the witness and the two effective residual-finiteness sequences supplied
by `positive-scaffold-has-quotient-compatible-rf-witness`.  They are exactly
the hypotheses of
`quotient-benign-rope-synchronizes-finite-quotients`, whose finite
coordinate-swap construction gives `(RPS2)` for every quotient in the
cofinal positive family.  This establishes `(RPS1)` for the unchanged graph
edge and is uniform in the presentation index.
