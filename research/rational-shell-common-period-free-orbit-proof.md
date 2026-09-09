---
rg: 2
id: rational-shell-common-period-free-orbit-proof
kind: route
title: Take a common period for the generator transducers and apply the free-orbit classification
target: rational-regular-shell-actions-require-virtually-cyclic-input
requires:
  - rational-shell-permutations-are-eventually-periodic
  - finite-ray-shift-envelopes-require-virtually-cyclic-input
  - shell-prefix-core-detects-finite-ray-enumerations
artifacts:
  - research/artifacts/boone-higman-arithmetic-shell-benchmark-2026-09-08.md
---

If the finitely many shell generators are rational, their shell
permutations rho_g have eventual periods m_g by the first required
claim. Take m to be a common multiple of these periods. Each
rho_g is eventually m-periodic. Such permutations are closed
under products and inverses: on the m residue rays they permute
the rays and translate ray coordinates after finitely many points.
Thus rho(P) is contained in the eventually m-periodic permutation
group. It has the even integers as a free orbit. The free-orbit
classification makes P virtually cyclic, proving (2) implies (1).

For a virtually cyclic input, the signed cyclic-coset enumeration
from the prefix-core claim makes all rho_g eventually 4d-periodic,
where d is the cyclic index. The rational-shell characterization
then makes every hat(g) rational. V is rational, and rational
homeomorphisms form a group, so E_nu is a rational subgroup in
this action. This proves (1) implies (3). The implication (3)
implies (2) is immediate from containment of the shell generators.

The argument concerns the given suffix-preserving shell maps.
Conjugating by an arbitrary homeomorphism, or choosing another
action of the abstract input group, is outside this classification.
