---
rg: 2
id: gromov-density-random-groups-hyperbolic-aspherical
kind: claim
title: Below density one half a Gromov random group is infinite hyperbolic with an aspherical presentation
distinct_from:
  torsion-free-hyperbolic-kazhdan-partner-exists: that is existence of one finitely presented torsion-free non-elementary hyperbolic Kazhdan group; this is the density-model theorem giving hyperbolicity and an aspherical presentation for most presentations below density one half, with no Kazhdan clause.
artifacts:
  - research/artifacts/density-random-groups-b2-verified-2026-09-12.md
---

**ESTABLISHED (literature import).** Fix `m >= 2` and `d ∈ (0, 1/2)`. Let `R`
be a uniformly random set of `⌊(2m−1)^{dℓ}⌋` cyclically reduced words of length
`ℓ` in `a_1^{±1}, …, a_m^{±1}`, and `G = <a_1, …, a_m | R>`. With probability
tending to 1 as `ℓ → ∞`:

- `G` is infinite and word-hyperbolic;
- the presentation is aspherical: there is no reduced spherical van Kampen
  diagram, the Cayley complex is aspherical, so the presentation 2-complex is a
  finite `K(G,1)`, `cd(G) <= 2`, and `G` is torsion-free.

Source: Y. Ollivier, *Sharp phase transition theorems for hyperbolicity of
random groups*, GAFA 14 (2004), arXiv:math/0301187v3, **Theorem 1** (Gromov's
density theorem), whose complete proof (Section 2 of the source) also proves the
asphericity. Quoted in the artifact.
