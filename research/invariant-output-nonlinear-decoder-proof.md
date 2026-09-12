---
rg: 2
id: invariant-output-nonlinear-decoder-proof
kind: route
title: Compare degree-one parts of the decoder identity and take augmentations
target: invariant-output-automata-have-only-nonlinear-decoders
requires: []
---

Algebraic normal forms over `F_2` are unique on every finite Boolean cube, and
shifting variables by `s` preserves degree. A linear decoder composed with any
encoder therefore has degree-one part `d a`, where `a` is the encoder's
degree-one coefficient vector. Right `H`-invariance of the output makes `a`
constant on free left `H`-orbits, so its augmentation is `0`. The required
identity `d a = 1` is impossible under the augmentation homomorphism.
