---
rg: 2
id: mf-safe-finite-presentation-compiler-via-doubles
kind: route
title: Rebuild Higman rope compression from MF-safe doubles and amenable edge moves
target: mf-safe-finite-presentation-compiler
requires:
  - symmetric-double-weak-mf
  - amenable-amalgams-have-mf-full-cstar
  - regular-mf-symmetric-doubles-are-regular-mf
  - amenable-amalgams-are-regular-mf
  - mf-safe-asymmetric-hnn-replacement
artifacts:
  - research/artifacts/mf-recognition-fp-pi2-completeness-2026-08-25.md
---

Refactor the effective rope/compression construction so every operation on the
`W_e`-infinite branch is known to preserve MF.  The allowed library should
start with free products, symmetric doubles `A *_C A`, amenable amalgams, and
central HNN moves covered by Shulman's theorem.  It must still expose an
embedded surviving copy of `E` when the c.e. stream stabilizes.

The hard point was asymmetric identification.  A generic Higman step identifies
two differently embedded subgroups by an HNN stable letter; no current MF
permanence theorem covers that operation.  A successful route must replace
each such identification by a symmetric double/diagonal gadget and prove both
its effective finite-presentation semantics and its MF permanence.  The cited
asymmetric-edge theorem now performs this step by adjoining the fixed
finite-CEP graph witness and tensoring its finite swap models with the
regular-MF model retained by the preceding safe moves.

Concretely, use the three-generator bridge so that the positive value is
`B3(1)`, intersect the ordinary benign witness with the graph witness in
`F_2 times F_2`, and apply the unchanged Higman rope.  The intersection is
still the recursive kernel because every branch kernel lies inside the
positive kernel.  Symmetric doubles, amenable amalgams, and central HNN moves
retain the regular character through the pre-rope construction; tensor
synchronization handles the one graph-valued final edge.  On the negative
branch the same witness and Britton normal form embed the surviving `E`.
