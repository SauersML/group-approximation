---
rg: 2
id: eilenberg-ganea-or-whitehead-is-false
kind: claim
title: At least one of the Eilenberg--Ganea conjecture and the Whitehead asphericity conjecture is false
distinct_from:
  eilenberg-ganea-conjecture: that asserts the Eilenberg--Ganea conjecture; this asserts only that it or the Whitehead conjecture fails, without deciding which.
  whitehead-asphericity-conjecture: that asserts the Whitehead conjecture; this asserts only that it or the Eilenberg--Ganea conjecture fails, without deciding which.
  acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead: that proves the same dichotomy for every acyclic non-aspherical finite flag 2-complex; this is the import for a spine of the Poincaré homology sphere.
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**ESTABLISHED** by literature import
`eilenberg-ganea-or-whitehead-bestvina-brady-citation`.

Let `L` be a flag triangulation of a spine of the Poincaré homology sphere,
`G_L` the right-angled Artin group of the 1-skeleton of `L`, and `H_L` the
kernel of the homomorphism `G_L -> Z` sending every standard generator to `1`.
Then either `H_L` has cohomological dimension 2 and geometric dimension
different from 2, so it is a counterexample to `eilenberg-ganea-conjecture`,
or some connected subcomplex of a contractible 2-complex is not aspherical, so
`whitehead-asphericity-conjecture` fails.

Which alternative holds is open:
`bestvina-brady-poincare-kernel-has-geometric-dimension-three` versus
`bestvina-brady-poincare-kernel-has-geometric-dimension-two`.
