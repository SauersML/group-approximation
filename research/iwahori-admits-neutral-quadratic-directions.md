---
rg: 2
id: iwahori-admits-neutral-quadratic-directions
kind: claim
title: The Iwahori mismatch map admits flat neutral directions whose quadratic term cancels the blocked residual
distinct_from:
  iwahori-second-order-repair-space-is-empty: that proves no such direction exists at a compatible pair, nor after padding by compatible blocks; this asks for one at pairs whose defect is small but whose distance to the compatible locus is not, where that proof gives nothing.
  iwahori-uniform-infinitesimal-rigidity: that is a lower bound on the first-order image at compatible pairs and says nothing about the kernel's second-order behaviour; this asks for a direction inside the kernel with a prescribed second-order effect.
  iwahori-outlier-repair: that proposes to convert a low-energy operator space into an exact invertible edge intertwiner after sublinear padding; this proposes a differential-geometric correction step and asks only for the direction, not for the intertwiner.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**OPEN.**  In the chart of `iwahori-second-order-repair-space-is-empty`, write
`F` for the mismatch residual, `L = DF(pi)`, and `Pi` for a projection onto a
complement of `ran L`.  Call a tangent direction `X` **`kappa`-flat** if
`||X||_(6,d) <= kappa ||X||_(2,d)`; by monotonicity of normalized Schatten
norms this also gives `||X||_(4,d) <= kappa ||X||_(2,d)`, i.e. bounded
effective rank in the sense of
`word-taylor-remainder-has-a-fourth-moment-bound`.

Ask for constants `C, kappa, eps, B`, independent of dimension, such that every
pair `pi` in dimension `d` with `e = def(pi) <= eps` admits, after adjoining at
most `r <= B e d` dimensions carrying exact vertex representations, an
admissible direction `xi` with

```text
L xi = 0,       ||xi||_(2,d) <= C sqrt e,       xi is kappa-flat,
|| Pi ( F(pi) + (1/2) D^2F(pi)[xi, xi] ) ||_(2,d) <= C e^(3/2),         (NQ1)
```

and such that the linear correction `eta` of `(SO2)` built from a right inverse
of `L` on `ran L` satisfies `||eta||_(2,d) <= C e` and is `kappa`-flat too.

Flatness is not decoration.  `D^2F` and `D^3F` have no dimension-free bounds in
normalized Hilbert-Schmidt norm at all
(`normalized-hs-taylor-remainder-is-not-dimension-free`), and the fourth- and
sixth-moment Hoelder estimates that do hold turn into usable ones exactly on
the flat cone.  A spiked correction fails the step even when its normalized HS
size is right.

By `second-order-step-beats-a-blocked-linearization` this yields the repair step
`iwahori-uniform-quadratic-repair-step`.

## Attempts

- **Not at the compatible locus, and not by compatible padding.**
  `iwahori-second-order-repair-space-is-empty` proves the projected quadratic
  form vanishes identically on `ker L` at every compatible pair, and that
  padding with representations of `SL_2(Z[1/2])` changes nothing, because
  `(UIR)` still identifies the kernel with the diagonal coboundaries there.  By
  continuity of `D^2F` the form stays small near that locus.  So any proof must
  produce directions at pairs bounded away from the compatible locus, and pad
  with vertex representations that are *not* restrictions of a common
  `SL_2(Z[1/2])` representation.  That is the noncongruence far sector.
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
  the linear theory identifies near the compatible locus are coboundaries
  `delta x`, whose spectral profile is that of `x`; making them flat is free
  there, but they pay nothing at second order.  Far from the locus nothing is
  known about `ker L`, and a direction found by optimization will generically
  concentrate, which is exactly what `(WT3)` penalizes.  A construction has to
  produce both properties at once.
- **Deferred:** no construction is attempted here.  The bet is recorded because
  the first-order theory has a proved uniform floor only in the near sector,
  the far sector has resisted every linear method in this lane, and the
  second-order mechanism is the first genuinely new degree of freedom proposed
  for it -- with the screen above saying exactly where it must live.
