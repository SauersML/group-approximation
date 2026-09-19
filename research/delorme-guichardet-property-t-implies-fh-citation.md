---
rg: 2
id: delorme-guichardet-property-t-implies-fh-citation
kind: route
title: Import Theorem 2.12.4, Propositions 2.2.9-2.2.10, Definition 2.7.5 and the proper-cocycle definition from Bekka-de la Harpe-Valette
target: delorme-guichardet-property-t-implies-fh
requires: []
---

**Citation.** Read 2026-09-19 from the authors' PDF of B. Bekka, P. de la Harpe,
A. Valette, *Kazhdan's property (T)*, New Math. Monographs 11, Cambridge UP 2008
(perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf). Printed page numbers.

* p. 79 (Chapter 2 opening): "a topological group G is said to have Property
  (FH) if every continuous action of G by affine isometries on a real Hilbert
  space has a fixed point". Also: "Let α be an affine isometric action of a
  topological group G on a real Hilbert space H, with linear part π and
  translation part b. Then π is an orthogonal representation of G and
  g ↦ b(g) is a 1-cocycle with coefficients in π".
* p. 86, Proposition 2.2.9: "Let π be an orthogonal representation of the
  topological group G on a real Hilbert space H. Let b ∈ Z^1(G,π), with
  associated affine isometric action α. The following properties are
  equivalent: (i) b belongs to B^1(G,π); (ii) b is bounded; (iii) all the
  orbits of α are bounded; (iv) some orbit of α is bounded; (v) α has a fixed
  point in H."
* p. 86, Proposition 2.2.10: "Let G be a topological group. The following
  properties are equivalent: (i) G has Property (FH); (ii) H^1(G,π) = 0 for
  every orthogonal representation π of G."
* p. 111 (after Theorem 2.7.1): "the cocycle b is a proper cocycle on G, that
  is, for every bounded subset B of H, the set b^{-1}(B) is relatively compact
  in G."
* p. 112, Definition 2.7.5: "A topological group G has the Haagerup Property,
  or is a-T-menable in the sense of Gromov, if there exists an orthogonal
  representation π of G which has a proper 1-cocycle b ∈ Z^1(G,π)." The text
  continues: "The class of groups with the Haagerup Property is a large class
  containing, moreover, amenable groups, free groups, Coxeter groups, and groups
  of automorphisms of locally finite trees [CCJJV–01]."
* p. 139, Theorem 2.12.4 (Delorme-Guichardet): "Let G be a topological group.
  (i) If G has Property (T), then G has Property (FH). (ii) If G is a σ-compact
  locally compact group and if G has Property (FH), then G has Property (T)."

**Derivation of items 2 and 3.** For a continuous homomorphism `f : H → G`
and `b ∈ Z^1(G,π)`, the map `b ∘ f` is continuous and satisfies the cocycle
identity for `π ∘ f`. So it lies in `Z^1(H, π ∘ f)`. By 2.12.4(i), 2.2.10 and
2.2.9 ((i) ⇒ (ii)), `b ∘ f` is bounded, say by `R`. With `B` the ball of radius
`R`, `f(H) ⊆ b^{-1}(B)`, which is relatively compact when `b` is proper.
