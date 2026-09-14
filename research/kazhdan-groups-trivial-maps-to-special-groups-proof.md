---
rg: 2
id: kazhdan-groups-trivial-maps-to-special-groups-proof
kind: route
title: A Kazhdan image in a special group fixes a point of the universal cover, hence is finite, hence trivial
target: kazhdan-groups-map-trivially-to-torsion-free-special-groups
requires:
  - niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes
---

**Proof of 1.** Let `X` be a compact special cube complex with
`pi_1(X) = H_0`. Put `N_0 = phi^(-1)(H_0)`, of finite index in `N`. A
finite-index subgroup of a group with property (T) has property (T)
(de la Harpe--Valette; standard, not re-read). `X` is nonpositively curved, so
its universal cover `X~` is a CAT(0) cube complex (Gromov's link condition;
standard, not re-read). It is finite dimensional because `X` has finitely many
cubes. `H_0` acts on `X~` cellularly by deck transformations, freely and
properly discontinuously.

`N_0` acts on `X~` through `phi`, cellularly. By
`niblo-reeves-kazhdan-groups-fix-points-on-cube-complexes` there is a global
fixed point `p`. A deck transformation fixing a point of `X~` is the identity:
the action on the geometric realization is free, since a nontrivial deck
transformation of a covering space has no fixed point. So
`phi(N_0) = 1`.

Then `phi(N)` has order at most `[N : N_0]`, so it is a finite subgroup of the
torsion-free group `H`, hence trivial.

**Proof of 2.** Suppose `(H_n, S_n) -> (N, S)`, with each `H_n` torsion-free
and virtually compact special. `N` is finitely presented by relators of length
at most `L`, so for large `n` every relator holds in `H_n` and
`S -> S_n` extends to a homomorphism `phi_n: N -> H_n`. By item 1, `phi_n` is
trivial. But convergence makes `phi_n` injective on the ball of radius `1` for
large `n`, and that ball contains `1` and a nontrivial generator, because `N`
is infinite. This is a contradiction.
