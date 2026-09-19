---
rg: 2
id: stw99-problem-xxxvi-phillips-toms
kind: claim
title: Radius of comparison of minimal Z-crossed products is half the mean dimension (STW Problem XXXVI, Phillips-Toms)
root: true
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

**Problem XXXVI of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Phillips--Toms conjecture; cf. the introduction to Niu's CJM paper).
For a minimal action `α : Z ↷ X`, is
`rc(C(X) ⋊_α Z) = mdim(α)/2`?

## Attempts

* The two inequalities have completely different characters.  `≤` is
  the quantitative refinement of Elliott--Niu (`mdim = 0` ⟹
  `Z`-stable ⟹ `rc = 0`) and is the direction Niu's
  small-boundary/Rokhlin-tower technology addresses; `≥` needs
  perforation PRODUCED by mean dimension, i.e. a characteristic-class
  witness inside the crossed product, known only for the
  Giol--Kerr/Phillips--Toms skew-product families where the base
  carries explicit Chern obstructions.  The mod-`ell` coordinate
  machinery of the XXVII lane
  (`stw27-coordinate-euler-slack-obstructs-compact-dividers`) is a
  ready-made lower-bound tool: it bounds dividers, hence comparison,
  purely from coordinate multiplicity data of the towers, and a
  dynamical version (towers of the first-return maps in place of
  Villadsen branch maps) would attack `≥` beyond skew products.
* A refutation is likelier on `≥`: a minimal system of positive mean
  dimension whose return-time combinatorics scramble every coordinate
  class (an entropy-style mixing killing Chern data) would give
  `rc < mdim/2`; no such construction exists, but nothing excludes it.
