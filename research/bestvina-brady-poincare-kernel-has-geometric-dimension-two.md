---
rg: 2
id: bestvina-brady-poincare-kernel-has-geometric-dimension-two
kind: claim
title: The Bestvina--Brady kernel of a Poincaré-sphere spine has a 2-dimensional Eilenberg--MacLane space
distinct_from:
  bestvina-brady-poincare-kernel-has-geometric-dimension-three: that is the complementary alternative, which refutes Eilenberg--Ganea; this one yields a counterexample to the Whitehead conjecture.
  eilenberg-ganea-or-whitehead-is-false: that is the established dichotomy; this decides one side of it.
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**OPEN.** Let `L` be a flag triangulation of a spine of the Poincaré homology
sphere and `H_L` the Bestvina--Brady kernel. There is a contractible 2-complex
on which `H_L` acts freely, properly and cellularly.

If established, it gives
`nonaspherical-subcomplex-of-contractible-2-complex-exists` through
`nonaspherical-subcomplex-via-bestvina-brady-kernel`, so
`whitehead-asphericity-conjecture` fails.

## Attempts

1. **Necessary shape (2026-09-13).** Any such complex has infinitely many
   `H_L`-orbits of cells, because `H_L` is not finitely presented. Equivariant
   cell-attachment to the level set `X_t` kills its fundamental group, a free
   product of binary icosahedral groups, but creates free `Z H_L`-summands in
   `pi_2`. Removing them is exactly the Eilenberg--Ganea obstruction: every
   countable group of cohomological dimension 2 has presentation complexes with
   free `pi_2`, by an Eilenberg swindle. So the natural construction gives no
   information here.
