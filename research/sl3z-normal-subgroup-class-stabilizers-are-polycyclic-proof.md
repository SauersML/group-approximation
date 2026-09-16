---
rg: 2
id: sl3z-normal-subgroup-class-stabilizers-are-polycyclic-proof
kind: route
title: Identify the class stabilizer with a centralizer modulo its intersection with N
target: sl3z-normal-subgroup-class-stabilizers-are-polycyclic
requires:
  - sl3z-infinite-order-centralizers-are-solvable
artifacts:
  - research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md
---

**The action.** `g . [x]_N := [g x g^-1]_N` is well defined. If
`x' = n x n^-1` with `n in N`, then
`g x' g^-1 = (g n g^-1)(g x g^-1)(g n g^-1)^-1`, and `g n g^-1 in N` because `N`
is normal. Elements of `N` fix every class, so the action descends to `G/N`.

**The stabilizer.**

- Elements of `N` and of `C_G(x)` fix `[x]_N`.
- Conversely, suppose `g x g^-1 = n x n^-1` with `n in N`. Then
  `n^-1 g in C_G(x)`, so `g in N C_G(x)`.
- So `Stab_G([x]_N) = N C_G(x)`. This is a subgroup because `N` is normal.
- The second isomorphism theorem gives
  `N C_G(x)/N ≅ C_G(x)/(C_G(x) ∩ N) = C_G(x)/C_N(x)`.
- For a subgroup `A <= N`, replace "commutes with `x`" by "normalizes `A`":
  `Stab_G([A]_N) = N N_G(A)` and `Stab_{G/N}([A]_N) ≅ N_G(A)/N_N(A)`.

**Polycyclicity.** If `x` has infinite order, then
`C_G(x) <= C_{SL_3(Z)}(x)` is solvable, hence polycyclic, by
`sl3z-infinite-order-centralizers-are-solvable`. Subgroups and quotients of
polycyclic groups are polycyclic, so `C_G(x)/C_N(x)` is polycyclic.

**Consequences.**

- If the orbit of `[x]_N` is finite, its stabilizer has finite index in
  `G/N`, so `G/N` is virtually polycyclic.
- If `G/N` is free, the stabilizer is free (Nielsen–Schreier) and solvable.
  A free group of rank at least 2 is not solvable, so the stabilizer is
  trivial or infinite cyclic.
