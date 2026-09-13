---
rg: 2
id: surface-torelli-not-fp-for-infinitely-many-genera
kind: claim
title: "For infinitely many g the Torelli group of the closed genus g surface is not finitely presented"
---

Let `I_g = ker(Mod(S_g) -> Sp_{2g}(Z))` for the closed oriented surface `S_g`. The
claim: `I_g` is not finitely presented for infinitely many `g`. It is the no-answer
for the surface family of Zaremsky Problem 3.1
(`zaremsky-3-01-surface-torelli-resolved`), and the negation of
`surface-torelli-groups-fp-for-large-genus`.

Known failures: `I_2` is not finitely generated (McCullough–Miller; Mess shows it
is an infinitely generated free group). No genus `g >= 3` is known to fail.

## Attempts

- **Top-degree homology.** Bestvina–Bux–Margalit (arXiv:0709.0287, abstract) show
  that for `g >= 2` the top homology `H_{3g-5}(I_g; Z)` is infinitely generated,
  so `I_g` is not of type `FP_{3g-5}`. Where it dies: `3g - 5 >= 4` for `g >= 3`,
  far above degree 2.
- **Degree 2 homology.** A no-answer by homology in degree 2 is now excluded for
  `g >= 4`: `H_2(I_g; Z)` is finitely generated there (Gaifullin,
  arXiv:2606.13517, Theorem A, preprint). Genus 3 is not covered, because Theorem A
  needs `k <= g - 2`. Where it dies: any uniform no-answer must use an invariant
  finer than `H_2`, for example a relation module that is not finitely generated
  (failure of `FP_2`), or a non-homological argument.
- **Genus 3 evidence.** Gaifullin (arXiv:2011.00295) shows that the term
  `E^3_{0,2}` of the spectral sequence for the action of `I_3` on the complex of
  cycles is infinitely generated. The abstract frames this as partial evidence
  toward `I_3` not being finitely presented. A single genus does not answer this
  claim, but a proof for `I_3` would land as its own partial claim.
