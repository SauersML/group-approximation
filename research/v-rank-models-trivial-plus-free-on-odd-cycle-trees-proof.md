---
rg: 2
id: v-rank-models-trivial-plus-free-on-odd-cycle-trees-proof
kind: route
title: Conjugacy of clopen p-cycles and Fourier inversion force a trivial-plus-regular torsion spectrum
target: v-rank-models-are-trivial-plus-free-on-odd-cycle-trees
requires: []
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/thompson-v-rank-models-torsion-spectra-2026-09-12.md
---

The proof is Section 1 of the artifact.

- **Lemma 1.1.** Any two clopen `p`-cycles are conjugate in `V`. Match one piece and the complements by
  prefix bijections, and transport along the cycles.
- **Lemma 1.2.** Every nonidentity element of a dyadic tree group `E_n` is a clopen `p`-cycle.
- **Theorem 1.3.**
  - The isotypic idempotents of a clopen-cycle subgroup `P` are orthogonal and sum to `1`, so their ranks
    form a probability measure on the dual of `P`.
  - Conjugacy invariance of rank, together with Lemma 1.1, makes the eigenvalue masses of `sigma(g)` the
    same for every clopen `p`-cycle `g`. Since `g^j` is conjugate to `g`, they are constant on the
    nontrivial roots.
  - The Fourier transform of the measure is therefore constant off the identity, and Fourier inversion
    gives `a delta_1 + (1 - a) uniform`.
  - Positivity over tree groups of unbounded order gives `0 <= a <= 1`.

*Verification by `w3-vf-linear` (2026-09-12), Section 20.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed Lemma 1.1, including the wrap at k = p−1; the tree-group commutation; and Lemma 1.2. In Theorem 1.3, recomputed steps 1–7: e_(g^j, zeta^j) = e_(g,zeta), the transform c − (1−c)/(p−1) = a off the identity, 0 <= a <= 1 from |E_n| unbounded, and rank (1−a)(p−1)/p. Proposition 2.1 and the slope invariant (Section 20.2) also PASS.*
