---
rg: 2
id: mf-safe-finite-presentation-compiler-via-doubles
kind: route
title: Rebuild Higman rope compression from MF-safe doubles and amenable edge moves
target: mf-safe-finite-presentation-compiler
requires:
  - symmetric-double-weak-mf
  - amenable-amalgams-have-mf-full-cstar
  - mf-safe-asymmetric-hnn-replacement
---

Refactor the effective rope/compression construction so every operation on the
`W_e`-infinite branch is known to preserve MF.  The allowed library should
start with free products, symmetric doubles `A *_C A`, amenable amalgams, and
central HNN moves covered by Shulman's theorem.  It must still expose an
embedded surviving copy of `E` when the c.e. stream stabilizes.

The hard point is asymmetric identification.  A generic Higman step identifies
two differently embedded subgroups by an HNN stable letter; no current MF
permanence theorem covers that operation.  A successful route must replace
each such identification by a symmetric double/diagonal gadget and prove both
its effective finite-presentation semantics and its MF permanence.  Merely
embedding the recursive group is insufficient.
