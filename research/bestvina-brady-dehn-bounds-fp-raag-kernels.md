---
rg: 2
id: bestvina-brady-dehn-bounds-fp-raag-kernels
kind: claim
title: The Bestvina–Brady Dehn function bounds below the Dehn function of every finitely presented kernel of a RAAG onto Z
refuted_by:
  - raag-kernel-dehn-function-below-bestvina-brady
distinct_from:
  bestvina-brady-dehn-bounds-kernels-with-no-dead-vertices: that claim restricts to characters nonzero on every vertex and is open; this one quantifies over all characters and is refuted
  bestvina-brady-dehn-bound-holds-up-to-quadratic: that claim proves the bound only when the Bestvina–Brady Dehn function is at most quadratic; this one asserts it in every degree
---

For every finite simplicial graph `Γ` and every surjective homomorphism
`χ : A_Γ → Z` whose kernel `K_χ` is finitely presented,
`δ_{BB_Γ} ≼ δ_{K_χ}`.

This is the affirmative answer to Zaremsky Problem 1.23
(`zaremsky-1-23-bestvina-brady-dehn-lower-bound`). It is false:
`raag-kernel-dehn-function-below-bestvina-brady` gives `Γ` with
`δ_{BB_Γ} ≃ n^3` and a finitely presented kernel with quadratic Dehn function.

## Attempts

- Refuted 2026-09-13 (unreviewed) by the suspension of the path on four vertices with the suspension vertices dead; see the refuting claim.
- True in degrees at most 2: `bestvina-brady-dehn-bound-holds-up-to-quadratic`.
