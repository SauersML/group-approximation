---
rg: 2
id: rigid-toeplitz-wire-nets-thick-rank-gradient-proof
kind: route
title: "Lift the wire net through the finite covering Λ → Γ\\Λ; connectivity makes its loops generate Γ, and an Euler count bounds its size by the rank of Γ"
target: rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient
requires:
  - quantum-rigid-subshifts-are-determined-by-thick-collars
  - fpbs-abert-nikolov-rank-gradient-equals-profinite-cost
---

Lane proof by bh-ra-proof, 2026-09-19. Not independently reviewed. The argument is the `## Proof` section of
`rigid-toeplitz-wire-nets-are-thick-over-positive-rank-gradient`. It uses:
- item 6 of `quantum-rigid-subshifts-are-determined-by-thick-collars` (the wire net exists, is connected
  and is `Γ`-invariant);
- the imported Abért–Nikolov identity (rank gradient = cost − 1 for Farber chains), for the reading in
  terms of cost.

The covering-space monodromy count and Schreier's bound for the monotonicity of `(d(Γ) − 1)/[Λ:Γ]`
are recalled, not re-read.
