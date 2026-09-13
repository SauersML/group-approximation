---
rg: 2
id: zaremsky-1-23-bestvina-brady-dehn-lower-bound
kind: claim
title: "Zaremsky Problem 1.23 resolved: does the Bestvina–Brady Dehn function bound below every finitely presented kernel of a RAAG onto Z?"
root: true
distinct_from:
  bestvina-brady-dehn-bounds-fp-raag-kernels: that claim is the affirmative answer; this is the question, established by either answer
  raag-kernel-dehn-function-below-bestvina-brady: that claim is the negative answer; this is the question, established by either answer
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 23, verbatim:
"(Added 1/20/26) For a right-angled Artin group AΓ, it turns out that if some
kernel of a map onto Z is finitely presented then specifically the
Bestvina–Brady kernel BBΓ is finitely presented. Does something similar happen
with Dehn functions? That is, does the Dehn function of BBΓ serve as a lower
bound for the Dehn functions of all finitely presented kernels of maps onto Z?"

This claim is the question. It is established only through an answer route:
- **Yes**: `zaremsky-1-23-by-yes` requires `bestvina-brady-dehn-bounds-fp-raag-kernels`.
- **No**: `zaremsky-1-23-by-no` requires `raag-kernel-dehn-function-below-bestvina-brady`.
Never write a `requires: []` route into this claim.

**Reading.** `Γ` is a finite simplicial graph, `A_Γ` its right-angled Artin
group, `BB_Γ` the kernel of the character sending every standard generator to
`1`, and a "kernel of a map onto Z" is `K_χ = ker χ` for a surjective
homomorphism `χ : A_Γ → Z`. Dehn functions are compared up to the usual
equivalence: `f ≼ g` when `f(n) ≤ C g(Cn + C) + Cn + C` for some `C`. The
question asks whether `δ_{BB_Γ} ≼ δ_{K_χ}` for every `Γ` and every `χ` with
`K_χ` finitely presented. The literal question allows characters that vanish
on some vertices ("dead" vertices), and the negative answer uses such a
character. The version restricted to characters that are nonzero on every
vertex is the open claim `bestvina-brady-dehn-bounds-kernels-with-no-dead-vertices`.

**Known input.** Chang, García-Mejía and Migliorini (arXiv:2507.07566, GAFA 36
(2026)) classify the Dehn functions of finitely presented Bestvina–Brady
groups: they are `n^d` with `d ∈ {1,2,3,4}` read off the graph
(`bestvina-brady-dehn-function-classification`).

**Status (2026-09-13, unreviewed).** Answered negatively: for `Γ` the
suspension of the path on four vertices, `BB_Γ` has cubic Dehn function, while
the kernel of the character that kills the two suspension vertices is
`F_2 × F_3`, with quadratic Dehn function. The lower bound does hold whenever
`δ_{BB_Γ} ≼ n^2` (`bestvina-brady-dehn-bound-holds-up-to-quadratic`).

## Attempts

- 2026-09-13 (lane z1-23-bb-dehn): counterexample `raag-kernel-dehn-function-below-bestvina-brady`, a join with a dead irreducible factor; awaiting review.
- Degrees 1 and 2 of the classification satisfy the bound for every finitely presented kernel, since every such kernel contains `Z^2` when `Γ` is not a tree.
