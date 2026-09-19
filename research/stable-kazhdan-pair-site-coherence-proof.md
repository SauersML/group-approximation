---
rg: 2
id: stable-kazhdan-pair-site-coherence-proof
kind: route
title: Exactify the acting tuple, Reynolds-project the lamp, and conjugate finitely many orbital checks
target: hs-stable-kazhdan-finite-bi-index-pair-gives-site-coherence
requires:
  - scaled-kazhdan-transport
---

Round the approximate involutions and the central marked projection by
functional calculus.  Almost centrality makes the marked block almost
invariant; block-diagonal polar correction changes each acting generator by
the square root of that leakage.  Apply the assumed same-dimension HS
stability of `L` separately on the retained block to obtain `sigma`.

The finitely many stabilizer generators are fixed words, so replacing the
acting generators by `sigma(S)` changes their commutators with the lamp by a
fixed multiple of the generator correction.  Apply the adjoint Kazhdan
projection estimate from `scaled-kazhdan-transport` to obtain `(SKC1)`.
The conditional expectation is self-adjoint and contractive.  Since its image
of the rounded lamp is close to an involution, spectral sign rounding remains
in `Comm(sigma(H))` and has the same order of error.

For `uH!=vH`, write `u^(-1)v=h_1 g_j h_2` for one of the finitely many
nontrivial double-coset representatives.  Exact `H`-centrality of `A` removes
`h_1,h_2`; exact multiplicativity of `sigma` reduces the pair to the `j`th
base relation.  Conjugation by `sigma(u h_1)` preserves normalized HS norm,
so no representative length enters the estimate.  This proves uniform site
coherence.
