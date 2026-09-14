---
rg: 2
id: simple-model-weak-soficity-with-small-defect-is-lef
kind: claim
title: Weak soficity by finite simple models with defect below c over the model size forces LEF
distinct_from:
  weakly-sofic-groups-are-surjunctive: that asks for surjunctivity from weak soficity with no constraint on the models or the defect rate; this collapses a constrained regime of weak soficity to local embeddability, and so is a statement about approximation classes rather than about cellular automata.
  regular-action-makes-weak-sofic-defects-maximal: that computes the Hamming length of one action; this bounds the given bi-invariant length from below using simplicity of the model.
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

**Length bound.** Let `H` be a finite simple group and `l` a
conjugation-invariant length on `H` with `l(x_0) >= c` for some `x_0`. Then

```text
l(k) >= c / |H|     for every k != 1.
```

**Collapse.** Let `G` admit, for every finite `F` in `G`, a weakly sofic
approximation `(H_F, l_F, phi_F)` with a fixed separation `c > 0`, with `H_F`
finite simple, and with defect `eps_F < c/|H_F|`. Then every defect is
trivial, so `phi_F` is an injective homomorphism on `F`. Hence `G` is LEF, and
therefore sofic and surjunctive.

**What this does not say.** Weak soficity constrains only `eps -> 0`, with the
model size unconstrained, and `c/|H|` shrinks with the model. So this does not
collapse weak soficity to LEF. Its use is to locate the room: on simple models
every bit of metric content sits in the window `c/|H| <= eps -> 0`. A proof
that weakly sofic groups are surjunctive must therefore use defects that decay
no faster than the reciprocal of the model size, or models far from simple,
where the length can be small on a large normal subgroup.
