---
rg: 2
id: kun-thom-wreath-carries-rigid-defect
kind: claim
title: The Kun--Thom coset wreath has a nontrivial rigid compression defect
distinct_from:
  wreath-not-sofic: that is nonsoficity of the coset wreath; this is the elementary group-theoretic fact that its root lamp produces a nontrivial rigid defect, which gives nonsoficity through the defect criterion and non-hyperlinearity on one branch of the Hilbert--Schmidt win--win.
  kun-thom-wreath-factor-is-exact-nonnormalized-commutant: that proves normalization fails in the wreath's own group von Neumann algebra; this is the group-level defect element, with no operator algebra.
  kun-thom-nonsofic-wreath: that imports the pair and Theorem A; this computes one commutator in the wreath over that pair.
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

**ESTABLISHED.** Let `Gamma < G` be the Theorem E pair: both Kazhdan, `Gamma`
infranormal and not normal in `G`. Put

```text
W = (direct_sum_(G/Gamma) Z/2) semidirect G,
```

with `e_x` the lamp at coset `x`. Then `Gamma <= G <= W` is a rigid pair and
its defect is nontrivial:

```text
[t e_Gamma t^-1, gamma] = e_(t Gamma) e_(gamma t Gamma) != 1
      for a strict compressor t and gamma in Gamma \ t Gamma t^-1.
```

- **A strict compressor exists.** If every compressor normalized `Gamma`,
  `G = <P_Gamma>` would normalize `Gamma`.
- **The root lamp centralizes `Gamma`.** `e_Gamma` is fixed by `Gamma`.
- **The lamps differ.** `gamma t Gamma = t Gamma` would mean
  `gamma in t Gamma t^-1`.

The computation uses only that `Gamma` is infranormal and not normal, so
every non-normal infranormal Kazhdan pair gives the same conclusion.

**Consumers.**

- **Sofic:** Kun--Thom Theorem A follows through
  `sofic-groups-kill-rigid-compression-defects`.
- **Weakly sofic:** `weakly-sofic-groups-can-carry-rigid-defects`.
- **Hyperlinear:** the non-hyperlinear branch of
  `hyperlinear-groups-kill-rigid-compression-defects`.

Derivation: `kun-thom-wreath-carries-rigid-defect-proof`.
