---
rg: 2
id: sitewise-pairs-over-prime-fields-are-stably-formalizable
kind: claim
title: Every sitewise bijective pair over a prime-field alphabet is formalizable after adding one identity track
distinct_from:
  binary-left-inverse-pairs-are-formalizable: that is open for arbitrary memories over F_2^n; this settles the sitewise case over every prime field, with the exact stabilization needed.
  multilinear-collapse-defect-does-not-obstruct-bijectivity: that is a characteristic-two calibration of representatives; this is the classification of which sitewise pairs over F_p are formalizable before and after stabilization.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

Let `p` be prime, `n >= 1`, `G` any group, and `(tau, sigma)` a sitewise bijective pair on
`(F_p^n)^G`: memory `{1}`, local permutation `phi`, `sigma = phi^-1`.

1. If `n >= 2` or `p <= 3`, the pair is formalizable.
2. If `n = 1` and `p >= 5`, the pair is formalizable iff `phi` is affine.
3. After adding one identity track, every such pair is formalizable.

So the prime-field analogue of `binary-left-inverse-pairs-are-formalizable` must allow stabilization.
It is recorded as `prime-field-left-inverse-pairs-are-stably-formalizable`.

Proof: Section 4 of the artifact.
