---
rg: 2
id: grigorchuk-group-center-and-out-citation
kind: route
title: Import the trivial center and the outer automorphism group of the first Grigorchuk group from Grigorchuk and Sidki
target: grigorchuk-group-has-trivial-center-and-elementary-abelian-out
requires: []
---

Literature import. Source: R. I. Grigorchuk and S. N. Sidki, *The group of automorphisms of a
3-generated 2-group of intermediate growth*, Internat. J. Algebra Comput. 14 (2004); author PDF
`people.tamu.edu/~grigorch/publications/sidkigrig3.pdf`, fetched on MSI 2026-09-13 and converted
to text with ghostscript. The published journal version was not read.

- The group: p. 1, "the 3-generated infinite 2-group G(2) constructed by the first author and
  shown to have intermediate growth", i.e. the first Grigorchuk group.
- Item 1: p. 1, "The groups G(2),G(3) have trivial centers and therefore are isomorphic to their
  inner group of automorphisms." Section 3 repeats "Since the center of G is trivial".
- Item 2: p. 2, "Theorem 1. The group G(2) admits an infinite set of automorphisms of order 2
  which generate a group V such that AutG(2) = (InnG(2))V and OutG(2) is elementary abelian
  2-group of infinite rank."
- The abstract of the preprint prints "elementary abelian 3- group"; Theorem 1 states the
  2-group, and this import uses Theorem 1.
- "Every finitely generated subgroup is finite" is immediate: a finitely generated abelian group
  of exponent 2 is finite.

Independent check of item 1 from `grigorchuk-group-is-just-infinite-torsion-not-fp`: a
nontrivial center is a normal subgroup, hence of finite index; then `𝔊` would be virtually
abelian, finitely generated and torsion, hence finite, which it is not.
