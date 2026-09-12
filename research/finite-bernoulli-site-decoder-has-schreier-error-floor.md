---
rg: 2
id: finite-bernoulli-site-decoder-has-schreier-error-floor
kind: claim
title: Every finite Bernoulli site decoder has a Schreier-gap error floor
distinct_from:
  infinite-schreier-pvm-transport-kills-finite-mark: that starts with an abstract finite-support PVM; this identifies the PVM produced by an arbitrary nonlinear Bernoulli site decoder and computes its transport energy exactly as decoder failure probability.
  global-schreier-pvm-is-stronger-than-action-soficity: that rules out a global Schreier PVM and gives the invariant-measure firewall; this gives the quantitative factor-of-iid/cylinder consequence and excludes raw-relator-controlled finite polynomial or spectral extraction.
  fixed-commuting-lamps-have-robust-fourier-atoms: that constructs Boolean Fourier atoms for one fixed commuting lamp packet; this proves that no finite Boolean postprocessing of such atoms can turn them into an approximately equivariant site label below the Schreier gap.
---

ESTABLISHED. Let a finitely generated group `A` act transitively on a
countable set `X`, and let the symmetric generating set `S` give the
normalized Schreier operator a bottom gap `gamma>0`. On the Bernoulli space

```text
Omega={0,1}^X
```

with product measure, let `f:Omega -> X` be any measurable map with finite
image. Then

```text
(1/|S|) sum_(s in S)
 Pr[f(s omega) != s f(omega)] >= gamma.                 (BSD1)
```

In particular the estimate is independent of the cylinder radius, Boolean
degree, number of Fourier atoms, and size of the image of `f`.

Every finite polynomial or finite spectral construction from commuting raw
Bernoulli lamp projections is a cylinder construction: after passing to the
finite Boolean atoms on the coordinates that occur, a complete orthogonal
site-label output is exactly a map `f` as above. Therefore no such nonlinear
construction can have actor-equivariance error tending to zero. More
sharply, its covariance defect cannot be bounded by any fixed sum of only
the raw lamp, commutation, and actor-covariance relator defects. In the exact
Bernoulli crossed product all those relator defects vanish, while `(BSD1)`
leaves error at least `gamma`.

The same conclusion holds for arbitrary finite Borel postprocessing of a
finite lamp window, not merely for polynomial formulas. Thus increasing the
degree of a fixed-window polynomial, taking exact spectral projections, or
using every Boolean Fourier atom does not extract the missing Cartan site
labels. A successful arithmetic decoder must use an additional mixed-root
or conductor relation that fails in the exact raw Bernoulli model, or else
use genuinely matrix-dependent/non-Cartan information not represented by a
finite Bernoulli factor.
