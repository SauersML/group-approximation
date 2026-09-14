---
rg: 2
id: bestvina-brady-epsilon-map-conjecture
kind: claim
title: "Bestvina--Brady epsilon-map conjecture: small-fiber PL images of the Poincaré-sphere spine are the spine with 1- and 2-cells attached"
distinct_from:
  bestvina-brady-poincare-kernel-has-geometric-dimension-three: that is the Eilenberg--Ganea alternative for the kernel H_L; this is a statement about PL maps out of one finite 2-complex, which implies it through `epsilon-map-conjecture-gives-poincare-kernel-gd-three`.
  whitehead-asphericity-conjecture: that is about asphericity of subcomplexes; this is about the homotopy type of small-fiber images, and with `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear` it forbids any such image of the spine from lying in a contractible 2-complex.
artifacts:
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

**OPEN.** Bestvina--Brady, Invent. Math. 129 (1997), Remark on p. 470, verbatim:

"Fix a metric on L. We conjecture that there is ε > 0 such that if g : L → K is a surjective PL
ε-map, then K is homotopy equivalent to L with 1- and 2-cells attached. This conjecture implies
that the geometric dimension of H_L is 3."

## Status in the literature

T. Tâm Nguyên-Phan, *A remark on ε-maps in dimension 1*, arXiv:1907.12063v1 (2019), read from
the arXiv PDF, verbatim.
- They state the conjecture for every finite 2-complex: "Conjecture 1 (Bestvina-Brady). Let L be
  a finite 2-complex. Fix a metric on L. There is ε > 0 such that if g : L → K is a surjective,
  PL ε-map, then K is homotopy equivalent to L with 1-cells and 2-cells attached." A footnote
  defines ε-map: "A map is an ε-map if pre-images of points have diameters less than ε."
- On its status: "While Conjecture 1 might sound “obviously true”, it remains open."
- In dimension 1 the literal form holds, "for a rather dull reason, which is that such PL-quotients
  of a circle by ε-maps are graphs that are not trees, and such graphs are always circles with
  1-cells attached".
- The relative form fails. "Theorem 3. For each ε > 0, there is a surjective ε-map f : S1 → G to
  a graph G such that f is NOT a generator in a free basis in π1 (G)."

**Consequence for the route.** A version in which `L` must sit inside the cell-attachment model
through `g` itself already fails in dimension 1, so no route should rely on it.
`epsilon-map-conjecture-gives-poincare-kernel-gd-three` uses only the weak form (E), where the
homotopy equivalence need not restrict to `g`.

## Reading of the statement

- **L.** The Remark closes the section on Theorem 8.7, where `L` is a flag triangulation of a
  spine of the Poincaré homology sphere.
- **ε-map.** Read with the standard meaning: every point preimage has diameter less than ε. The
  quoted text does not define it.
- **Conclusion.** `K ≃ L ∪ (1-cells) ∪ (2-cells)`.

**Weak form (E).** `K` is homotopy equivalent to some 2-dimensional CW complex that contains `L`
as a subcomplex. The conjecture implies (E), and the route
`epsilon-map-conjecture-gives-poincare-kernel-gd-three` uses only (E), and only for the maps
`φ_v` in the proof of Theorem 8.7.

## What is known about small-fiber images

For ε below a Lebesgue number of the open-star cover of `L`, sending each vertex of a fine
triangulation of `K` to a point of its preimage and extending over skeleta inside contractible
open stars gives `λ: K → L` with `λ ∘ g ≃ id_L`. This is the construction in the proof of
Theorem 8.7. So `L` is a homotopy retract of `K`, and `g` is injective on `π_1` and `π_2`. The
conjecture asks for more, namely a cell-attachment model. See the artifact, §3.

## Strength

With `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`, even (E) implies that no
small-fiber PL image of the spine is a subcomplex of any contractible 2-complex. This is a
Whitehead-type statement, so settling the conjecture is not expected to be easier than the
relevant case of `whitehead-asphericity-conjecture`.
