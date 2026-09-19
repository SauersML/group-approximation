---
rg: 2
id: mf-symmetric-double-invariance-proof
kind: route
title: Combine Shulman's symmetric group-double theorem with subgroup heredity
target: mf-is-invariant-under-symmetric-doubling
requires:
  - mf-positive-controls
artifacts:
  - research/artifacts/property-t-free-mf-envelope-calculus-2026-08-30.md
  - research/artifacts/shulman-2603-13564-verified.md
---

The forward construction is a direct literature import.  Shulman,
[*The MF property for amalgamated free
products*](https://arxiv.org/html/2603.13564), Introduction after Theorem 10,
states:

> if `G` is an MF group, then any double `G *_H G` is MF.

This is the group-level consequence of her symmetric C-star theorem, not an
attempt to infer MF of `C*(G)` from group MF.  It applies to the weak/operator
norm matrix-corona convention used here; the paper's Definition 3 is exactly
embedding the group in the unitary group of a norm matrix corona.

Conversely, the normal-form theorem for amalgamated free products makes each
canonical map `G -> G *_H G` injective.  If the double is MF, its canonical
vertex copy of `G` is MF by subgroup heredity in `mf-positive-controls`.
This proves `(MSD1)`.  No Property `(T)` or approximation rigidity enters
either implication.  ∎
