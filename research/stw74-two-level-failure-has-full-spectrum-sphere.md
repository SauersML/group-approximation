---
rg: 2
id: stw74-two-level-failure-has-full-spectrum-sphere
kind: claim
title: A level-two descent failure splits the unit into two positive contractions with projectionless hereditary subalgebras
distinct_from:
  stw74-projectionless-corner-forces-gapless-compressions: that says nonzero scalar compressions of a projection over a projectionless corner have 0 as a spectral accumulation point; this chooses a subprojection equivalent to the unit, obtains norm exactly 1 and spectrum [0,1], and proves that both complementary supports e and 1-e have projectionless hereditary subalgebras.
  stw74-minimal-projection-has-uniform-gapless-compressions: that gives a uniform norm floor delta for compressions of a minimal-level projection; this works at level two, gets norm 1 for the whole sphere, and adds the unit-splitting characterization of (SP).
  stw74-lxxiv-hinge-is-two-level-descent: that reduces (SP) to level-two descent; this describes the structure a level-two failure is forced to carry and deduces the unit-splitting dichotomy from it.
artifacts:
  - research/artifacts/stw74-two-level-descent-2026-09-16.md
---

Let `A` be a unital simple C\*-algebra in which every nonzero projection is
infinite, let `H` be a hereditary C\*-subalgebra of `A` with no nonzero
projection, and suppose `M_2(H)` contains a nonzero projection.

1. There are `x,y in A` with `x*x+y*y=1` and `xx*, xy*, yx*, yy* in H`.
2. For every unit vector `xi in C^2`, put `z_xi=conj(xi_1)x+conj(xi_2)y`,
   `b_xi=z_xi z_xi* in H` and `e_xi=z_xi* z_xi`.  Then `e_xi+e_eta=1` for
   orthonormal `xi,eta`, and `sigma(e_xi)=sigma(b_xi)=[0,1]`; in particular
   `||b_xi||=1` on the whole sphere.
3. For every unit vector `xi`, `Her_A(e_xi)` contains no nonzero projection.
   In particular `Her(x*x)` and `Her(1-x*x)=Her(y*y)` are both
   projectionless.

Consequently (unit-splitting dichotomy): such an algebra `A` has (SP) if and
only if for every positive contraction `e in A` at least one of `Her(e)` and
`Her(1-e)` contains a nonzero projection.
