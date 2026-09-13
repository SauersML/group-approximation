---
rg: 2
id: bestvina-brady-dehn-bound-holds-up-to-quadratic
kind: claim
title: If the Bestvina–Brady Dehn function is at most quadratic, it bounds below every finitely presented kernel of the RAAG onto Z
distinct_from:
  bestvina-brady-dehn-bounds-kernels-with-no-dead-vertices: that claim is the open lower bound for characters nonzero on every vertex in every degree; this one is the proved lower bound for all characters when d(Γ) ≤ 2
---

Let `Γ` be a finite simplicial graph with `d(Γ) ≤ 2` in the sense of
`bestvina-brady-dehn-function-classification`: `Δ(Γ)` is simply connected and
`Γ` has neither property (D3) nor (D4). Then `δ_{BB_Γ} ≼ δ_{K_χ}` for every
surjective `χ : A_Γ → Z` with `K_χ = ker χ` finitely presented.

Combined with `raag-kernel-dehn-function-below-bestvina-brady` (a cubic
counterexample), this shows that degree 3 is the first degree where the
lower bound in Zaremsky Problem 1.23 can fail. Whether it fails in degree 4 for
some graph is not recorded here.

Established by `bestvina-brady-dehn-bound-holds-up-to-quadratic-proof`,
unreviewed as of 2026-09-13.
