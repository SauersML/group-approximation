---
rg: 2
id: iwahori-admits-neutral-quadratic-directions
kind: claim
title: The Iwahori mismatch map admits flat neutral directions whose quadratic term cancels the blocked residual
distinct_from:
  iwahori-second-order-repair-space-is-empty: that computes the projected quadratic form at exact compatible pairs; this asks for controlled admissible corrections at all pairs of sufficiently small defect, including inexact ones.
  iwahori-uniform-infinitesimal-rigidity: that is a lower bound on the first-order image at compatible pairs and says nothing about the kernel's second-order behaviour; this asks for a direction inside the kernel with a prescribed second-order effect.
  iwahori-outlier-repair: that proposes to convert a low-energy operator space into an exact invertible edge intertwiner after sublinear padding; this proposes a differential-geometric correction step and asks only for the direction, not for the intertwiner.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**OPEN.** This asks for both a neutral direction and a uniformly controlled
parameterization that keeps the two vertex representations exact.
Call a matrix-tuple parameter `X` **`kappa`-flat** if
`||X||_(6,d) <= kappa ||X||_(2,d)`; by monotonicity of normalized Schatten
norms this also gives `||X||_(4,d) <= kappa ||X||_(2,d)`, i.e. effective
rank bounded below in the sense of
`word-taylor-remainder-has-a-fourth-moment-bound`.

Ask for constants `C, kappa, eps, B`, independent of dimension, such that every
pair `pi` in dimension `d` with `e = def(pi) <= eps` admits the following
data. Adjoin at most `r <= B e d` dimensions carrying exact vertex
representations, obtaining `pi_tilde` with `def(pi_tilde) <= C e`.
Supply a smooth map `Psi` from a finite-dimensional space of matrix-tuple
parameters into exact vertex-representation pairs, with `Psi(0)=pi_tilde`.
Write `F` for the mismatch residual composed with `Psi`, `L=DF(0)`,
and `Pi` for a projection killing `ran L` onto a complement of that range.
Require a right inverse `R` of `L` on its range, with `||R||` and
`||I-Pi||` bounded by `C`. All norms below use dimension `d+r`.
There are parameters `xi` and `eta` satisfying

```text
L xi = 0,       ||xi||_2 <= C sqrt e,       xi is kappa-flat,
|| Pi ( F(0) + (1/2) D^2F(0)[xi, xi] ) ||_2 <= C e^(3/2),             (NQ1)
```

where `eta` is the linear correction `(SO2)`, has `||eta||_2 <= C e`,
and is `kappa`-flat too. For `v=xi+eta`, require that `Psi` is defined
near the segment `tv`, `0<=t<=1`, and that

```text
||D^2F(0)[X,Y]||_2 <= C ||X||_4 ||Y||_4       (X,Y in {xi,eta}),
||D^3F(tv)[v,v,v]||_2 <= C ||v||_6^3          (0<=t<=1),
max_s d_0(Psi(v)_s, pi_tilde_s) <= C (||xi||_2+||eta||_2).           (NQ2)
```

These chart, derivative, and padding-defect requirements are part of the
open problem. Smoothness in each dimension does not supply them uniformly.
Independent generator exponentials need not preserve the vertex relations,
and arbitrary inexact padding need not keep defect `O(e)`.

Flatness is not decoration.  `D^2F` and `D^3F` have no dimension-free bounds in
normalized Hilbert-Schmidt norm at all
(`normalized-hs-taylor-remainder-is-not-dimension-free`), and the fourth- and
sixth-moment Hoelder estimates that do hold turn into usable ones exactly on
the flat cone.  A spiked correction fails the step even when its normalized HS
size is right.

By `second-order-step-beats-a-blocked-linearization` this yields the repair step
`iwahori-uniform-quadratic-repair-step`.

## Attempts

- **Exact-point screen.**
  `iwahori-second-order-repair-space-is-empty` proves the projected quadratic
  form vanishes identically on `ker L` at every compatible pair, and that
  padding with representations of `SL_2(Z[1/2])` changes nothing, because
  `(UIR)` still identifies the kernel with the diagonal coboundaries there.
  Exact pairs have zero residual and admit the zero correction. The screen
  neither excludes corrections near that locus nor forces inexact padding;
  its dimension-independent extension off the exact locus is not proved.
- **A convex cone of quadratic effects is not a direction.**  Membership of
  `-Pi F(pi)` in the convex hull of `{Pi D^2F[xi, xi] : xi in ker L}` is weaker
  than `(NQ1)`: summing directions creates cross terms, and the fluid
  construction this transfer came from controls those by genuinely separated
  spatial supports.  A matrix realization needs its own synthesis, on the
  original space or with the padding already counted; a semidefinite relaxation
  does not supply one.
- **The one place this archive searched, it found nothing.**  The exact
  8,600-direction Hessian screen recorded in
  `research/artifacts/atlas-flip-translation-sector-hessian-screen.md` scanned
  the translation sector at the Atlas flip with gauge directions excluded and
  found no direction of negative loss curvature, the active slice being exactly
  flat.  Different problem, but it is the only completed search of this kind
  here and its answer was negative.
- **Flatness and neutrality pull against each other.**  The kernel directions
  the linear theory identifies at the compatible locus are coboundaries
  `delta x`; these have zero projected quadratic effect there. Flatness of
  a potential does not automatically give relative flatness of its
  coboundary, whose HS norm may be much smaller. Away from the exact locus
  a construction has to
  produce both properties at once.
- **Deferred:** no construction is attempted here.  The bet is recorded because
  the first-order theory has a proved uniform floor only in the near sector,
  the far sector has resisted every linear method in this lane, and the
  second-order mechanism is a proposed additional degree of freedom. The
  screen above evaluates it only at exact compatible points.
