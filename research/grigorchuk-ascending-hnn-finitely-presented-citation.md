---
rg: 2
id: grigorchuk-ascending-hnn-finitely-presented-citation
kind: route
title: Import Grigorchuk's finitely presented ascending HNN extension of the first Grigorchuk group
target: grigorchuk-ascending-hnn-extension-is-finitely-presented
requires: []
---

Literature import plus one line of derivation. Source read from the PDF of
L. Bartholdi, R. I. Grigorchuk, Z. Šunić, *Branch groups*, arXiv:math/0510294v2,
on 2026-09-13.

- p. 55, "The 'first Grigorchuk group'": the ascending L-presentation
  `𝔊 = < a, c, d || phi | a^2, [d, d^a], [d^{ac}, (d^{ac})^a] >` with
  `phi(a) = aca`, `phi(c) = cd`, `phi(d) = c`.
- Theorem 4.9 (Grigorchuk, [Gri98]), p. 56, verbatim: "There exists a finitely
  presented amenable group that is not elementarily amenable." Its proof:
  "form the HNN extension H amalgamating 𝔊 with φ(𝔊). It is an ascending HNN
  extension, so H is amenable; and H admits the (ordinary) finite presentation
  H = ⟨a, c, d, t | a², [d, d^a], [d^{ac}, d^{aca}], a^t aca, c^t cd, d^t c⟩."
  An HNN extension amalgamating 𝔊 with φ(𝔊) presupposes that `phi: 𝔊 -> φ(𝔊)`
  is an isomorphism, i.e. that `phi` is an injective endomorphism.
- Ol'shanskii–Sapir (arXiv:math/0208237, p. 4) independently record that "the
  first example of a finitely presented group which is a cyclic extension of an
  infinite torsion group was constructed by Grigorchuk [15]".

Derivation of `phi(G) <= St_G(1)`: `c`, `d` and `cd` lie in `St_G(1)`, and so does
`aca`, since `St_G(1)` is normal. The images of the generators `a, c, d` are
`aca, cd, c`, so `phi(G) <= St_G(1)`. Since `a` is not in `St_G(1)`
(`grigorchuk-group-is-just-infinite-torsion-not-fp`), `phi` is not surjective.
