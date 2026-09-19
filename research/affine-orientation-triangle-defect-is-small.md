---
rg: 2
id: affine-orientation-triangle-defect-is-small
kind: claim
title: Noise and boundedness force the product-uniform affine orientation defect to be small
distinct_from:
  affine-orientation-glue-lemma: that is the global conclusion the soundness decoder consumes, a bounded hitting set for heavy cosets; this is the purely local estimate on one random affine plane and asserts nothing about a global label list.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
  - research/artifacts/approximation-cs-root-audit-2026-08-31.md
---

**OPEN.**  The analytic half of `affine-orientation-glue-lemma`.

Keep the notation of that node: `f : {-1,1}^Omega -> [-1,1]`, `g = T_rho f`,
and for each `b` in a positive-density set `B subset Omega \ {0}` a
`(d, delta)`-heavy coset `C_b = q_b + <b>` of the quotient `D_b`.  The exact
interface required downstream is product-uniform sampling on `B x B`: the
analytic step must certify a set `S subset B x B` of density `1-o(1)` such
that every `(b,c) in S` carries a point common to `C_b` and `C_c`.  A stronger
certificate, when a selected line in direction `b+c` is available, is

```text
C_b,   C_c,   C_{b+c}
```

with a common point on all three lines.  Call failure of the relevant
concurrency certificate the **orientation-defect event**.

```text
star:      C_b intersect C_c intersect C_{b+c} != empty.
```

The former wording said that arbitrary selected lines admit "exactly two
configurations", a star or a triangle inside the plane they span.  That is
false in ambient dimension at least three: selected affine lines may be
skew, and `C_(b+c)` is not even defined unless `b+c` lies in the selected
direction set or the selector has been extended.  Those cases must be
counted as defect, not silently identified with an affine triangle.  Also,
conditioning on an irregular set of additive triples changes the marginal
on `B` and is not sufficient for the uniform hitting conclusion.

**Statement.**  For every fixed `rho, d, delta, alpha > 0`, the selected
heavy cosets on every `B` of density at least `alpha` admit star certificates
on a `1-o(1)` fraction of product-uniform pairs in `B x B`, with the defect
bounded by a function of the fixed parameters alone that tends to zero.

The three-line star case is a cocycle condition: it says the chosen coset
representatives agree at a point.  Nonconcurrent, skew, or unavailable-sum
configurations are all part of the defect unless the proof supplies a
separate completion.  By
`triangle-defect-globalizes-to-a-bounded-label-list`, product-uniform star
density immediately gives the bounded list; the whole remaining burden is
therefore this analytic density estimate.  Its content is that high **noisy
restricted** influence cannot be supported on many mutually inconsistent
chosen cosets.

Why this is the right place to spend boundedness.  A single direction can
be memorized with all three of boundedness, low degree and noise intact
(`linear-pairing-memorizer-restricts-to-a-dictator`), and any number of
directions can be memorized inside vanishing ambient `L^2`
(`affine-memorizers-are-cross-direction-orthogonal`).  Neither construction
says anything about whether the memorized cosets in *different* directions
can be placed inconsistently.  So cross-direction compatibility is the first
quantity in this circle of ideas that boundedness has a chance to control.

## Attempts

* **Direct Fourier expansion of the plane statistic.**  Expanding
  `g|_{D_b}`, `g|_{D_c}`, `g|_{D_{b+c}}` in the three different quotient
  bases and correlating them is the obvious move.  Where it dies: the three
  restrictions live on three different subcubes and the natural correlation
  is not a single Fourier expression; a common refinement is the quotient
  by `<b,c>`, in which every one of the three singleton characters becomes
  a non-singleton, so the statistic is not a low-degree correlation of
  low-degree objects.
* **Invariance principle on the plane quotient.**  Push all three to the
  `F_2^2`-quotient and apply a multi-slice or Gaussian invariance
  principle.  Where it dies: invariance needs small influences in the
  quotient, and heaviness is the hypothesis that one quotient influence is
  *large*.  The escape clause has to be extracted before invariance, not
  after, and how to do that is exactly what is unknown.
* **Borrow the 2-to-2 machinery.**  The proved 2-to-2 Games Theorem
  controls an analogous consistency statistic, but at completeness near
  `1/2`; `unique-constraints-orient-at-most-half-of-a-fiber` explains
  structurally why `1/2` is where that family of arguments stops, so it is
  not expected to transfer without a new idea.
