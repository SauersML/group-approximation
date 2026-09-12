---
rg: 2
id: maximal-stabilizer-hnn-commutant-equivalence-proof
kind: route
title: Use maximality to turn an arbitrary spectral projection leak into exact subgroup separation
target: maximal-subgroup-hnn-equals-commutant-collapse
requires:
  - commutation-stabilizers-are-relatively-embeddable
  - relative-embedding-is-commutant-separation
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
artifacts:
  - research/artifacts/commutation-stabilizer-relative-embedding-2026-09-07.md
---

If the two commutants differ, choose a self-adjoint element in their
difference and a spectral projection moved by some actor element.
Its commutation stabilizer `K` contains `C` and is proper in `A`,
hence equals `C` by maximality. Apply the stabilizer extraction
theorem and the scalar-RE/HNN equivalence.

In the converse direction, HNN hyperlinearity yields the canonical
free binary coset-wreath model. Its base lamp commutes with `C` and
fails to commute with every actor element outside `C`, contradicting
global collapse. Section 4 of the artifact checks all embedding
quantifiers, spectral projections, and the case of an actor having
no canonical matrix-ultraproduct embedding.
