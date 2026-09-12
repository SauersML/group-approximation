---
rg: 2
id: rational-marker-involution-nonformalizable-proof
kind: route
title: The rationals have no proper finite-index subgroup and are bi-orderable, and the marker involution is not affine
target: marker-involution-over-rationals-is-not-virtually-formalizable
requires:
  - formalizable-binary-pairs-over-biorderable-groups-are-affine
artifacts:
  - research/artifacts/formalizability-by-shear-decomposition-2026-09-12.md
---

Section 5.3 of the artifact.
- **No regrouping.** `Q` is divisible, so a finite quotient `Q/H` of order `n` is divisible, and every
  class is `n` times a class, which is `0`. So `H = Q`, and the automaton keeps one track.
- **Bi-orderable.** `Q` is bi-orderable by its usual order.
- **Affine.** By the prerequisite, a formal pair would give `tau(x)(g) = x(g + m) + eps`.
- **Contradiction.** `tau` fixes the configuration with a single `1` at `0`, since every marker needs
  two `1`s. So `m = 0` and `eps = 0`, and `tau = id`. But `tau` changes the configuration that is `1`
  exactly at `−1` and `1`.
