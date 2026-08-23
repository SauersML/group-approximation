---
rg: 2
id: threshold-free-mf-compiler-equivalence-proof
kind: route
title: Use the dummy-generator switch in one direction and reverse Kleene in the other
target: threshold-free-mf-compiler-equivalence
requires:
  - marked-mf-radical-seed-gives-proof-triggered-compiler
  - threshold-free-reverse-kleene-mf-higman
  - mf-radical-functoriality
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
  - GroupApproximation/Computability/SeededSelfAwareMFCompiler.lean
---

A marked finitely presented seed gives the compiler by
`marked-mf-radical-seed-gives-proof-triggered-compiler`.

Conversely, apply `threshold-free-reverse-kleene-mf-higman` to any compiler
with the stated semantics. Its fixed-point group contains a nontrivial word
in the MF radical. Effective Higman embeds that recursively presented group
in a finitely presented group. Injectivity preserves nontriviality, while
`mf-radical-functoriality` preserves MF-radical membership. The image of the
fixed-point word is therefore the required marked finitely presented seed.

The logical fixed-point contradiction and both semantic directions are
independently checked in Lean. The Lean endpoint is deliberately named
`logicalSelfAwareMFCompiler_iff_seed`: recursive presentation codes and
Kleene's theorem are the external layer of this route.
