---
rg: 2
id: phase-safe-toric-via-central-word-state-face
kind: route
title: Compile the fixed non-RU trace into the relative finite-dimensional central-word face
target: phase-safe-toric-gap-game-exists
requires:
  - mipstar-bcs-tracial-nonru-exists
  - toric-gap-is-a-relative-fd-central-word-face
  - finite-morita-toricization-cannot-encode-nonaffine-support
  - central-word-state-face-compiler
---

Use the established BCS tracial/non-`R^U` separation as the source.  The
relative-FD face theorem identifies the exact target soundness statement and
the normal quotient formula identifies the syntax that survives phase-safe
groupification.  The remaining compiler must preserve the tracial source
face, decode every finite-dimensional target state back to the source, and
encode the predicates through centralizable player words.  Once it does,
the target toric game has `omega_qc=1>omega_qa` and its scalar phase survives
normal closure.
