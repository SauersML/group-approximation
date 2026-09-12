---
rg: 2
id: steinberg-flag-fox-map-is-injective-at-five-and-seven
kind: claim
title: The full Steinberg flag Fox map is injective in characteristics five and seven
artifacts:
  - research/artifacts/steinberg-fox-primes-3-5-7-2026-09-04.jsonl
distinct_from:
  steinberg-flag-fox-map-is-injective: that asks for every odd prime; this proves only the two specified prime instances by exact finite certificates.
  steinberg-zero-plane-transfer-closes-p-five: that assumes zero chord marginals; this checks the entire flag-incidence map, with no extra marginal hypothesis, at five and seven.
---

For `p=5` and `p=7`, the map `D_p` defined in
`steinberg-fox-kernel-is-flag-incidence` is injective.  In particular the two
Fox rows have zero common kernel on the full defining-characteristic
Steinberg module, including vectors with nonzero chord marginals.

Exact full-column minors of `D_5` and `D_7` have determinants `4 mod 5`
and `3 mod 7`, respectively.  The accompanying certificate specifies their
row indices, and the proof fixes every basis and matrix-entry convention.

This is a finite-case result, not a nonhyperlinearity theorem.  It neither
proves the all-prime claim nor supplies the normalized-Hilbert--Schmidt
stability needed to turn the arithmetic route into a nonhyperlinear group.

DERIVATION
steinberg-five-seven-full-minor-proof
