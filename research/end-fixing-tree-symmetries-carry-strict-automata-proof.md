---
rg: 2
id: end-fixing-tree-symmetries-carry-strict-automata-proof
kind: route
title: Copy the parent toward the fixed end and decode by the minimum over the two children
target: end-fixing-tree-symmetries-carry-strict-automata
requires: []
artifacts:
  - research/artifacts/gottschalk-tree-calibration-and-bernoulli-preservation-2026-09-12.md
  - research/artifacts/gk-vf-positive-verification-2026-09-12.md
---

Complete direct proof, Section 1 of the artifact.

* Automorphisms fixing `xi` commute with `p` and permute the children of each
  vertex. So `tau` and `sigma` are equivariant.
* On the image both children of `w` carry `x(w)`. So `sigma tau = id`, and two
  siblings with different symbols are never in the image.
* The Busemann character has as kernel an increasing union of compact open
  subgroups, so `Gamma` is amenable. Its modular function is `2` raised to that
  character, so `Gamma` is not unimodular.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 1.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
