---
rg: 2
id: strict-comparison-rank-surjectivity-sr1-citation
kind: route
title: Import Lin's Theorem 1.1 on strict comparison and stable rank one
target: strict-comparison-rank-surjectivity-forces-sr1
requires: []
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

**Established by citation.** Huaxin Lin, *Strict comparison and stable rank
one*, J. Funct. Anal. 289 (2025), 111065,
[arXiv:2301.09250v2](https://arxiv.org/abs/2301.09250). Theorem 1.1 of the
arXiv version, verbatim: "Let A be a sigma-unital non-elementary simple
C*-algebra with strict comparison (which is not purely infinite). Then the
following are equivalent: (1) The canonical map Gamma: Cu(A) ->
LAff_+(QT~(A)) is surjective. (2) A has tracial approximate oscillation zero.
Moreover, if (1) or (2) hold, then A has stable rank one."

The paper assumes `QT~(A) != {0}`. `LAff_+(S)` consists of pointwise
increasing limits of functions that are strictly positive continuous affine
or zero.

Identification with the Rank Problem, for unital separable exact `A`:

1. `T(A)` is a metrizable Choquet simplex.
2. Every lower semicontinuous affine `f: T(A) -> (0, infinity]` is an
   increasing limit of continuous affine functions (Edwards), which by
   compactness are eventually above `min f / 2`.
3. So restricted to normalized traces, `LAff_+` is zero together with all such
   `f`, and surjectivity of `Gamma` is the Problem XXIII conclusion.

Lin's introduction also records that it is not known whether every separable
amenable finite simple algebra with strict comparison has stable rank one.
