---
rg: 2
id: hs-centralizer-normalization-from-rigid-defects
kind: route
title: The Hilbert--Schmidt rigid defect criterion forces centralizer normalization in every matrix-ultraproduct representation
target: kt-centralizer-normalization-hs
requires: [hyperlinear-groups-kill-rigid-compression-defects, rigid-compression-defect-normalization-dichotomy]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

1. Let `sigma : G -> U(prod_U M_n)` be any homomorphism of an infranormal
   Kazhdan pair, trace-preserving or not.
2. Suppose some `g in G` and unitary `z` in the relative commutant have
   `sigma(g) z sigma(g)^-1` outside it.
3. The group `<sigma(G), z>` is a countable subgroup of the ultraproduct's
   unitary group, hence hyperlinear (inclusion `(+) 1` plus tensor
   amplification).
4. It contains the rigid pair `sigma(Gamma) <= sigma(G)`, and the element
   `z` gives a nontrivial rigid defect, contradicting the criterion.
5. Unitaries span the relative commutant, so `sigma(G)` normalizes it.

This is the `DD => NORM` half of the dichotomy. It yields normalization for
all homomorphisms, which contains the trace-preserving statement of
`kt-centralizer-normalization-hs`.

**Correction (2026-09-12).** The target node says that refuting it is
consistent with either answer to Q3.4. By the dichotomy and
`hyperlinear-nonsofic-via-hyperlinear-rigid-defect`, a refutation produces a
hyperlinear nonsofic group, so refuting it answers Q3.4 negatively. See the
artifact, Section 8.

**Cycle, on purpose.** This route and
`hs-rigid-defects-from-centralizer-normalization` record an equivalence;
see that route.
