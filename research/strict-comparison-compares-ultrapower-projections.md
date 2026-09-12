---
rg: 2
id: strict-comparison-compares-ultrapower-projections
kind: claim
title: Strict comparison compares projections by limit traces in every matrix amplification of the uniform tracial ultrapower
distinct_from:
  stw22-cpou-ii1-has-rr0-sr1-and-all-traces: that derives real rank zero, stable rank one and trace equality from complemented partitions of unity; this derives Murray--von Neumann comparison of projections from strict comparison of the C*-algebra, with no CPoU and no uniform Gamma.
  toms-gamma-counterexample-fails-strict-comparison: that shows every AH counterexample to uniform Gamma fails strict comparison, through all ranks almost occurring, Winter's purity theorem and CETWW; this is a structural statement for arbitrary exact algebras which excludes every projection-comparison certificate against Gamma.
artifacts:
  - research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md
---

Let `A` be a unital, simple, exact, non-elementary C*-algebra with nonempty
trace space and strict comparison of positive elements.  Let `A^omega` be its
uniform tracial ultrapower, and let `p, q` be projections in `M_k(A^omega)`
with `sigma(p) <= sigma(q)` for every limit trace `sigma`.  Then there is
`v in M_k(A^omega)` with `v* v = p` and `v v* <= q`.

In particular projections of the uniform tracial completion with
`tau(p) <= tau(q)` for all `tau in T(A)` are subequivalent in the ultrapower.
Equality of traces is allowed.

**Consequence.**  Every obstruction to uniform property Gamma which exhibits
projections with dominated traces that are not subequivalent in the tracial
ultrapower forces failure of strict comparison, whatever the building blocks.
Toms's Schubert-calculus certificate (arXiv:2606.12188v2, Theorems 2 and 5) is
of this kind: its proof only uses finite-stage uniform 2-norm approximants of a
putative partial isometry, which a partial isometry in `M_k(A^omega)` also
supplies.  So a strict-comparison algebra without uniform Gamma, which is what a
Toms--Winter counterexample must be, compares projections in its tracial
ultrapower exactly as a CPoU algebra does, and its failure of Gamma is invisible
to projection comparison.

The proof is in Section 1 of the artifact: lift to near projections, use the
quadratic spectral inequalities for ranks, add a Glimm witness of uniformly
small rank and uniformly positive trace so that strict comparison applies with
a gap, cut down with Rordam's lemma, compress the witness away, and diagonalize
over witnesses of rank `1/l`.  Reviewer PASS:
`research/artifacts/review-toms-winter-ultrapower-comparison-2026-09-12.md`.

**Literature status (2026-09-12, bounded search by lane `lit-scout`).**  No
source proving this statement was found.
- Every comparison-of-projections result found assumes complemented partitions
  of unity:
  - Carrion et al., arXiv:2310.20594v6, Theorems 7.5 and 7.17, for reduced
    products and tracially complete algebras with CPoU;
  - CETWW, arXiv:1901.05853, Lemma 4.3, which gives strict comparison of
    relative commutants in `B^omega` under CPoU.
- Without CPoU, the nearest results reported give only weak*-density of limit
  traces in the trace space of the ultrapower (Ozawa; Ng--Robert
  arXiv:1504.00046; not re-read here).  That is a different statement.
- The search was bounded, so novelty is not asserted.  This claim does not by
  itself give uniform Gamma; that step is the open
  `tracial-projection-comparison-forces-uniform-gamma`.
