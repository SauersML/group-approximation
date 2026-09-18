---
rg: 2
id: gl-n-q-type-a-via-projective-extension
kind: route
title: A projective type (A) overgroup of PGL_m(Q) for infinitely many m puts every GL_n(Q) in B_A
target: gl-n-q-in-permutational-boone-higman-class
requires:
  - pgl-q-projective-type-a-extension
  - gl-n-q-targets-are-cofinal-in-n
---

`pgl-q-projective-type-a-extension` gives, for infinitely many `m`, a finitely
presented group with a type (A) action containing `PGL_m(Q)`. So `PGL_m(Q)`
lies in the permutational class `B_A` for infinitely many `m`. By
`gl-n-q-targets-are-cofinal-in-n`, `PGL_m(Q)` for infinitely many `m` suffices
for every `GL_n(Q)`, because `GL_(m-1)(Q) ≤ PGL_m(Q)` and `B_A` is closed
under subgroups.
