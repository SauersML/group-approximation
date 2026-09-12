---
rg: 2
id: finitary-linear-permanence-proof
kind: route
title: Embed finite windows in a finite group times the actor, and kill finite normal subgroups by scalars
target: finitary-linear-extension-sofic-and-no-finite-normal-subgroup
requires: []
artifacts:
  - research/artifacts/compression-finitary-linear-action-theorem-2026-09-08.md
---

Section 2 of the artifact is a complete direct proof.

**Soficity.** A finite subset of `K x| N` lies in
`GL(F_2^O) x| N_0` with `N_0 <= N` finitely generated and `O` the
finite `N_0`-invariant union of the matrix supports, finite by the
orbit hypothesis. With `rho : N_0 -> Sym(O)`, the map
`(A,h) |-> ((A, rho(h)), h)` is an injective homomorphism into the
product of the finite group `GL(F_2^O) x| rho(N_0)` with `N_0`.
Soficity is closed under products, subgroups, directed unions, and
extensions with amenable quotient (Elek--Szabo, *On sofic groups*,
Theorem 1), which is the same citation
`dyadic-perturbation-soficity-proof` uses for the permutation family.

**Finite normal subgroups.** `K` has no nontrivial finite quotient: in
a finite quotient, pigeonhole over infinitely many `r` gives distinct
`r,s` outside `{i,j}` with `T_(ir)` and `T_(is)` equal, and then
`[T_(ir)T_(is)^-1, T_(rj)] = T_(ij)` dies, so conjugation kills every
transvection. A finite normal `F <= G` is therefore centralized by
`K`, since `K -> Aut(F)` has finite image. The representation
`(A,v) |-> A P_v` on `F_2^(X)` is faithful when every nonidentity
element of `V` moves infinitely many points, because `A P_v = I`
would make `P_v` finitary. Commuting with every off-diagonal matrix
unit forces an operator to be scalar, and `1` is the only invertible
scalar over `F_2`, so `F = 1`.

**Finite generation.** For a finite symmetric generating set `S` of
`V`, the transvections in both directions between `x_0` and each
`s x_0 != x_0`, together with their `V`-conjugates, form the directed
edges of a connected graph on `X` by transitivity, and
`[T_(ij), T_(jk)] = T_(ik)` along simple paths yields every
transvection.

**Simplicity of the kernel.** A nontrivial normal subgroup of `K` meets
some `GL_n(F_2)` nontrivially, so contains it by simplicity of
`GL_n(F_2) = SL_n(F_2)` for `n >= 3`, and then contains every later
stage of the directed union.
