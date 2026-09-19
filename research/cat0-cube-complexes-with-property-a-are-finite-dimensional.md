---
rg: 2
id: cat0-cube-complexes-with-property-a-are-finite-dimensional
kind: claim
title: The vertex set of an infinite-dimensional CAT(0) cube complex never has property A, because every cube is an isometric Hamming cube with a 1-Lipschitz gate retraction
distinct_from:
  cat0-cube-complexes-have-the-jensen-helly-property: that is a positive Jensen–Helly property for median graphs of finite cube dimension; this is a negative coarse property (failure of property A) forced by infinite cube dimension.
  stein-farley-height-fixes-a-roller-boundary-point: that kills amenable-action routes through the Roller boundary via a fixed point; this kills property A of the cube complex itself, with no boundary and no group action.
  nowak-hamming-cubes-have-property-a-arbitrarily-badly: that is the imported input about the cubes Q_n alone; this puts the cubes inside every infinite-dimensional CAT(0) cube complex with retractions.
---

**ESTABLISHED** through `cat0-cube-complexes-with-property-a-are-finite-dimensional-proof`.

Let `X` be a CAT(0) cube complex, not assumed locally finite or finite-dimensional. Give its vertex set `X⁽⁰⁾`
the edge-path metric of the 1-skeleton.

1. **Retraction lemma.** Let `C` be an `n`-cube of `X`.
   - The vertex set `Q = C⁽⁰⁾`, with the metric from `X⁽⁰⁾`, is isometric to the Hamming cube `{0,1}^n`.
   - There is a 1-Lipschitz retraction `π_C : X⁽⁰⁾ → Q`. It sends `y` to the vertex of `C` that lies on the
     same side as `y` of each of the `n` hyperplanes crossing `C`.
2. **Theorem.** If `X⁽⁰⁾` has Yu's property A, then `X` is finite-dimensional. Quantitatively, for every
   `0 < ε < 2`, `X` has no cube of dimension `n` with `diam^A_{Q_n}(1,ε) > diam^A_{X⁽⁰⁾}(1,ε)`.

**Remarks.**

- The converse is a theorem of Brodzki–Campbell–Guentner–Niblo–Wright. Verbatim from Guentner–Niblo,
  arXiv:1008.3925 (fetched 2026-09-18): "In previous work, in collaboration with J. Brodzki, S. Campbell and
  N. Wright, we showed that a finite dimensional CAT(0) cube complex has Property A". So *a CAT(0) cube complex
  has property A iff it is finite-dimensional*, modulo the local-finiteness hypotheses of that paper, which were
  not re-checked. The converse is not used here.
- `X⁽⁰⁾` always coarsely embeds into Hilbert space: `√d` is a Hilbert-space metric, because `d` is the
  `ℓ^1`-distance of hyperplane coordinates. So infinite-dimensional CAT(0) cube complexes are natural,
  group-equivariant instances of Nowak's phenomenon: coarsely embeddable, without property A.
