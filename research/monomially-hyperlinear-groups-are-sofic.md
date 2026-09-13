---
rg: 2
id: monomially-hyperlinear-groups-are-sofic
kind: claim
title: Every group with a regular monomial Hilbert--Schmidt model is sofic
distinct_from:
  block-monomial-hs-models-sofic-mod-amenable-soft-kernel: that proves such a group is sofic modulo an abelian normal subgroup; this asks that the abelian soft kernel never obstructs soficity.
  monomial-rank-models-are-sofic-over-every-field: that is the rank-metric version, established because rank sees exact phase agreement; this is the Hilbert--Schmidt version, where only approximate flatness of the phases is available.
  hyperlinear-groups-admit-masa-normalizing-microstates: that asks every hyperlinear group for frame-coherent microstates and is equivalent to Q3.4; this assumes frame-coherent microstates and asks for soficity group by group, which Q3.4 does not need.
artifacts:
  - research/artifacts/ex-q34-monomial-phases-2026-09-12.md
---

**OPEN.**  If a countable group `G` has regular HS models in
`U(1) wr S_n` (permutations carrying arbitrary phases), then `G` is sofic.

**What is known.**  The permutation kernel `A` of such a model is an abelian
normal subgroup, and `G/A` is sofic
(`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`).  So the claim
holds whenever `G` has no nontrivial abelian normal subgroup, and the whole
content is the abelian-by-sofic case.  If the phases can be made to satisfy
the relators *exactly* on most columns, the conclusion follows by the
character, torsion and skew-product argument of
`monomial-rank-models-are-sofic-over-every-field`.

**Stakes.**  A counterexample would be a hyperlinear nonsofic group.  A proof
never helps Q3.4: `hyperlinear-implies-sofic-via-frame-extraction` passes to
`H * Z`, which has no abelian normal subgroup, and needs no curvature control.
The Kun--Thom wreath `(Z/2) wr_(G/Gamma) G` is abelian-by-sofic and nonsofic
(`kun-thom-nonsofic-wreath`, preprint import).  So the claim predicts that it
has no regular monomial HS model.

## Attempts

- **Round the phases edgewise to `mu_m`.**  Dies on carries: rounding errors
  add along relator paths, and the holonomy is off by a small nonzero integer
  on a positive density of columns.  That is a full Hamming defect.
- **Loeb skew product `X × U(1)`.**  The limit cocycle is exact, and the skew
  product has fixed-point density `<= (1 + Re tau)/2` for every nontrivial
  element.  But it is a continuous circle extension with no finite model,
  which is the same problem.
- **Flatten the curvature (linearized).**  Solve `dB = F` on the good relator
  cells of the finite Schreier 2-complex with `||B|| = o(1)`, deleting `o(n)`
  cells.  Small 2-cycles carry zero flux automatically.  Large 2-cycles carry
  integer, Chern-type flux, removable by deleting a cell.  A band argument
  handles amenable directions at cost `O(|F|^(2/3))`, and an electrical flow
  handles directions with a 2-dimensional spectral gap.  Complexes combining
  low-frequency curvature modes with large 2-cycles are not handled.  This is
  the open core.
- **Model test on the Kun--Thom wreath.**  Models with every lamp in the soft
  kernel are excluded by `block-monomial-coordinate-collapse`.  Models whose
  soft kernel is a proper submodule of the lamp module are not covered.
  Their exclusion would need a Kun--Thom argument for quotient modules, and
  their existence would refute this claim.
