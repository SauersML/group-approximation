---
rg: 2
id: cat0-cube-loops-bound-quadratic-square-diagrams
kind: claim
title: A combinatorial loop of length L in a CAT(0) cube complex bounds a square disc diagram with at most L^2/8 squares, crossing only hyperplanes the loop crosses
---

**OPEN (literature import, not checked at source).** Let `X` be a CAT(0) cube
complex, of any dimension and not necessarily locally finite, and let `γ` be a
combinatorial loop of length `L`. Then `γ` bounds a disc diagram
`D -> X` whose 2-cells are squares, with:

1. **Dual curves.** Every square of `D` is the crossing of two dual curves.
   Each dual curve is an embedded arc with both ends on `∂D`. Two dual curves
   cross at most once. So `D` has at most `L/2` dual curves and at most
   `(L/2)(L/2 - 1)/2 <= L^2/8` squares.
2. **Hyperplanes.** Every hyperplane of `X` met by the image of `D` is met by
   `γ`.

**Source to check.** These are the standard minimal-diagram facts: in a
diagram of minimal area there are no monogons, bigons or closed dual curves.
They go back to Sageev (Proc. London Math. Soc. 71 (1995)) and are used
throughout Wise's work on cube complexes. Sageev's PCMI notes "CAT(0) cube
complexes and groups" (fetched 2026-09-13) give the hyperplane facts (§1.3,
line 334 of the text extraction) but not the disc diagram lemma. The
diagram-reduction lemma still has to be pinned in a primary source.

**Consequence used.** Item 2 plus "combinatorial distance = number of separating
hyperplanes" (Sageev) bounds the distance from any vertex of `D` to `γ` by
`L/2`.
