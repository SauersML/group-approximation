---
rg: 2
id: affine-orientation-triangle-defect-is-small
kind: claim
title: Noise and boundedness force the affine orientation cocycle defect on random F_2^2 planes to be small
distinct_from:
  affine-orientation-glue-lemma: that is the global conclusion the soundness decoder consumes, a bounded hitting set for heavy cosets; this is the purely local estimate on one random affine plane and asserts nothing about a global label list.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**OPEN.**  The local half of `affine-orientation-glue-lemma`, in its
geometric form.

Keep the notation of that node: `f : {-1,1}^Omega -> [-1,1]`, `g = T_rho f`,
and for `b != 0` a `(d, delta)`-heavy coset `C_b = q_b + <b>` of the
quotient `D_b`.  Draw `b, c` independently at random from `Omega \ {0}` and
look at the three lines

```text
C_b,   C_c,   C_{b+c}
```

inside the affine `F_2^2`-plane they span.  Exactly two configurations
occur:

```text
star:      C_b intersect C_c intersect C_{b+c} != empty
triangle:  the three lines are not concurrent.
```

Write the **triangle-defect probability** for the fraction of pairs `(b,c)`
landing in the second case.

**Statement.**  For every fixed `rho, d, delta > 0` the triangle-defect
probability is `o(1)` -- bounded by a function of `rho, d, delta` alone
that tends to 0 -- unless `f` has one of a bounded number of large ambient
low-degree influences.

The star case is a cocycle condition: it says the chosen coset
representatives `q_b` agree on the plane, so orientations composed around
the plane return to where they started.  Triangles are the cocycle defect.
The content of the statement is that high **noisy restricted** influence
cannot be supported on many triangle configurations without an ambient
coordinate becoming influential.

Why this is the right place to spend boundedness.  A single direction can
be memorized with all three of boundedness, low degree and noise intact
(`linear-pairing-memorizer-restricts-to-a-dictator`), and any number of
directions can be memorized inside vanishing ambient `L^2`
(`affine-memorizers-are-cross-direction-orthogonal`).  Neither construction
says anything about whether the memorized cosets in *different* directions
can be placed inconsistently inside a common plane, which is precisely what
a triangle asks.  So the pairwise/planar compatibility is the first
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
