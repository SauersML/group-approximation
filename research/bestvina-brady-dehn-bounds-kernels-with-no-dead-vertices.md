---
rg: 2
id: bestvina-brady-dehn-bounds-kernels-with-no-dead-vertices
kind: claim
title: The Bestvina–Brady Dehn function bounds below every finitely presented RAAG kernel whose character is nonzero on all vertices
distinct_from:
  bestvina-brady-dehn-bounds-fp-raag-kernels: that claim quantifies over all characters and is refuted by a character with dead vertices; this one keeps only characters nonzero on every vertex
---

For every finite simplicial graph `Γ` and every surjective `χ : A_Γ → Z` with
`χ(v) ≠ 0` for every vertex `v` and `ker χ` finitely presented,
`δ_{BB_Γ} ≼ δ_{ker χ}`.

This is Zaremsky Problem 1.23 restricted to the case the known counterexample
(`raag-kernel-dehn-function-below-bestvina-brady`) avoids. With no dead
vertices, the Meier–Meinert–VanWyk criterion shows `ker χ` is finitely
presented exactly when `Δ(Γ)` is simply connected, as for `BB_Γ`. A stronger
form is `δ_{ker χ} ≃ δ_{BB_Γ}` for all such `χ`.

## Attempts

- Characters with `χ(v) = ±1` for all `v`: the automorphism of `A_Γ` inverting the generators where `χ(v) = -1` maps `BB_Γ` onto `ker χ`, so the two kernels are isomorphic and the bound holds.
- Degree `d(Γ) ≤ 2`: the bound holds for every character (`bestvina-brady-dehn-bound-holds-up-to-quadratic`).
- General values: `ψ(v) = v^{±M/|χ(v)|}` with `M = lcm |χ(v)|` is injective and maps `BB_Γ` into `ker χ`, but the image is neither a retract nor of finite index, so it transfers no Dehn function bound. Next step: check whether the corridor and height arguments of Chang–García-Mejía–Migliorini (arXiv:2507.07566, the Section 6 lower bounds) use only that each generator has nonzero height, e.g. by rerunning them with the weighted height `χ`. Not yet attempted.
- Test object: `Γ = {A, B} * (C – D – E – F)` with `χ(A) = 1`, `χ(B) = 2` and `χ = 1` on the path. It is cubic if the lower bound transfers.
