---
rg: 2
id: bijective-ca-preserve-uniform-bernoulli-measure-proof
kind: route
title: Conjugate local permutations by the automaton and use that only the uniform measure is locally symmetric
target: bijective-ca-preserve-uniform-bernoulli-measure
requires: []
artifacts:
  - research/artifacts/gottschalk-product-trace-zero-one-law-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Section 2 of the artifact. With `sigma = tau^-1` of memory `M` and `tau` of memory
`N`, the homeomorphism `rho = sigma o pi o tau` for a local permutation `pi` on
`F` moves only coordinates in `F M^-1`. It reads those on
`E = (F M^-1 M ∪ F) N`, so it is a bijection of `A^E` times the identity and
preserves `mu`. Bijectivity gives `tau^-1(pi B) = rho(tau^-1 B)`, so `tau_* mu`
is invariant under every local permutation. Transpositions of patterns force
equal cylinder masses, hence `tau_* mu = mu`.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 20 of the
verification artifact). Injectivity of the finite map `r` comes from bijectivity
of `rho` on configurations that agree off `E`.
