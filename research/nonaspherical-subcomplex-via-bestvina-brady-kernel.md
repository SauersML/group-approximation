---
rg: 2
id: nonaspherical-subcomplex-via-bestvina-brady-kernel
kind: route
title: A 2-dimensional K(H_L,1) for the Poincaré-sphere spine gives a non-aspherical subcomplex of a contractible 2-complex
target: nonaspherical-subcomplex-of-contractible-2-complex-exists
requires:
  - bestvina-brady-poincare-kernel-has-geometric-dimension-two
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

Let `L` be a flag triangulation of a spine of the Poincaré homology sphere, and
`Y` a contractible 2-complex with a free, proper, cellular `H_L`-action, as the
required claim provides.

`L` is acyclic with fundamental group the binary icosahedral group of order
120. The source's computation reads `pi_2(L) = H_2(L~) != 0`, with `L~` the
3-sphere minus 120 points. Step 4 of `acyclic-nonaspherical-l-dichotomy-proof`
gives the same by Euler characteristic: rank `120 - 1`.

Step 3 of `acyclic-nonaspherical-l-dichotomy-proof` is the proof of
Bestvina--Brady Theorem 8.7 (pp. 469--470), and uses only `pi_2(L) != 0`. With
this `Y`, it produces a finite connected subcomplex `K` of a subdivision of
`Y` with `pi_2(L)` injecting into `pi_2(K)`. So `pi_2(K) != 0`. A subdivision
of a contractible 2-complex is a contractible 2-complex, which gives the target.
