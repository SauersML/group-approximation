---
rg: 2
id: hypergraph-absorption-schreier-matching
kind: claim
title: Absorption converts a codegree package into simultaneous generator matchings
artifacts:
  - research/artifacts/hyperlinear-divergent-strategies-2026-08-18.md
---

**Target (GSD-2 of the source dossier).**  There is a deterministic theorem of
the following shape: any coloured candidate hypergraph satisfying the
degree/codegree/divisibility package of
`spherical-candidate-hypergraph-quasirandom` admits a choice of one perfect
matching per generator colour such that, for every word `w` in the tested
window, the composed maps agree with the intended target on `1-o(1)` of the
roots.

This is the integrality engine of the design programme, and it is a statement
about hypergraphs only: no spheres, no unitaries, no group beyond the finite
labelling.  The available technology is the fractional-relaxation → nibble →
absorption pipeline of modern matching and design theory (Keevash,
arXiv:1807.05752, as a survey of what such theorems look like and what
hypotheses they need).

**The non-standard feature.**  Standard matching theorems produce *one*
perfect matching in *one* hypergraph.  Here several matchings — one per
generator — must be produced simultaneously, and the objective couples them
along words: the constraint is not on any single matching but on composites
`sigma_g ∘ sigma_h` versus `sigma_{gh}`.  So the absorbing structure has to
absorb defects of *composite* maps, and a naive colour-by-colour application
of an existing theorem gives matchings with no relation to each other — the
same failure as independent nearest-neighbour matching in
`geometric-schreier-design`, arrived at combinatorially instead of
geometrically.

## Attempts

- **Apply a hypergraph matching theorem once per colour.**  Dies as above: the
  theorems are indifferent to the composite constraints, and nothing couples
  the colours.
- **Encode the whole table as one hypergraph whose edges are complete local
  assignments, then take one perfect matching.**  This does couple the
  colours, but the edges then have size growing with the window and the
  codegree conditions required become conditions about long words, which
  `spherical-candidate-hypergraph-quasirandom` does not supply — the
  quasirandomness available is per-relation, not per-window.  Finding the
  right intermediate edge size is the open design decision.
- **Absorb only the relation defects, treating the matchings as given.**  This
  is the most promising version and is deferred rather than refuted: build the
  matchings greedily by nibble, keep a reservoir of vertices whose images are
  unassigned, and use the reservoir to repair the roots where
  `sigma_g sigma_h ≠ sigma_{gh}`.  The unresolved point is whether the
  reservoir can be made simultaneously absorbing for all tested relations,
  since repairing one relation at a root moves the images that another
  relation at the same root depends on.
