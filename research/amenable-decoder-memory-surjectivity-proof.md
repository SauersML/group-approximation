---
rg: 2
id: amenable-decoder-memory-surjectivity-proof
kind: route
title: Restrict the surjective decoder to its amenable memory group, apply the Garden of Eden theorem, and split
target: amenable-decoder-memory-forces-surjectivity
requires:
  - amenable-groups-satisfy-the-garden-of-eden-theorem
  - split-decoders-have-generic-cantor-fibers
  - table-groups-are-memory-holonomy-groups
artifacts:
  - research/artifacts/table-group-holonomy-normal-form-2026-09-12.md
---

**The theorem.**
- `sigma` has the right inverse `tau`, so it is surjective.
- It acts coset by coset on `G / <S>` by a copy of one automaton over `<S>`. That
  copy is surjective.
- `<S>` is amenable, so by the Garden of Eden theorem the copy is pre-injective.
- A distinct asymptotic pair with equal images would differ on one coset, which
  is impossible. So `sigma` is pre-injective over `G`.
- By `split-decoders-have-generic-cantor-fibers`, `sigma` is then bijective, and
  `tau = sigma^(-1)` is onto.

**The design filter.** Every realization with forward table `>= E` receives a
homomorphism from the table group mapping `Hol_S(E)` onto the decoder memory group,
and amenability passes to quotients.

Section 3 of the artifact.
