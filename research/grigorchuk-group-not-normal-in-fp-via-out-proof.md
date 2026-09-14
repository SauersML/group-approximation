---
rg: 2
id: grigorchuk-group-not-normal-in-fp-via-out-proof
kind: route
title: The first Grigorchuk group is not normal in a finitely presented group because its Out is locally finite
target: grigorchuk-group-is-a-normal-subgroup-of-no-fp-group
requires:
  - centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp
  - grigorchuk-group-has-trivial-center-and-elementary-abelian-out
  - grigorchuk-group-is-just-infinite-torsion-not-fp
---

Suppose `G` is finitely presented and `N ⊴ G` with `N ≅ 𝔊`.
- `N` has trivial center and every finitely generated subgroup of `Out(N)` is finite
  (`grigorchuk-group-has-trivial-center-and-elementary-abelian-out`).
- So `N` is finitely presented (`centerless-normal-subgroups-with-locally-finite-out-of-fp-are-fp`).
- But `𝔊` is not finitely presented (`grigorchuk-group-is-just-infinite-torsion-not-fp`),
  a contradiction.

Source note: Benli, *Indicable Groups and Endomorphic Presentations*, arXiv:1112.1764, TeX
l.498–502, verbatim: "I have been told by Mark Sapir (private communication) that not all finitely
generated recursively presented groups embed into finitely presented groups \textit{as normal
subgroups}. His example was the first Grigorchuk group."
