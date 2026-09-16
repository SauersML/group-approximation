---
rg: 2
id: sl3z-contains-f2-by-free-subgroup
kind: claim
title: SL_3(Z) contains a subgroup isomorphic to F_2 x| F_m for some m >= 2
refuted_by: sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients
distinct_from:
  sl3z-contains-f2-times-f2: that asks for the direct product, refuted by the commuting-subgroups obstruction; this asks for any semidirect product F_2 x| F_m, whose monodromy may be injective and which contains no F_2 x Z
  sl3z-contains-cd2-euler-positive-fibered-subgroup: that asks for a cd-two Euler-nonzero subgroup fibring over Z with finitely generated kernel, any fibre rank or type; this is the rank-two-fibre free-by-free special case, where incoherence would come from Kropholler–Walsh directly
---

`SL_3(Z)` contains a subgroup isomorphic to `F_2 x|_ψ F_m` for some `m >= 2`
and some homomorphism `ψ: F_m -> Aut(F_2)`.

Such a subgroup would make `SL_3(Z)` incoherent through the Kropholler–Walsh
theorem that every finite-index subgroup of `F_2 x| F_n` is incoherent; see the
route `sl3z-incoherent-via-f2-by-free-subgroup`.

Refuted. A subgroup of `SL_3(Z)` with a normal subgroup isomorphic to `F_2`
has a finite or virtually infinite cyclic quotient
(`sl3z-normal-f2-subgroups-have-virtually-cyclic-quotients`), and `F_m` with
`m >= 2` is neither.

## Attempts

- 2026-09-16 (hi-fron-zaremsky-3-04-sl3z-coherent): refuted.
  - Every automorphism of `F_2` sends `[a, b]` to a conjugate of
    `[a, b]^{±1}`.
  - So an index-at-most-two subgroup of the quotient stabilizes the
    `F_2`-conjugacy class of `[a, b]`. That stabilizer is
    `C_G([a, b])/C_{F_2}([a, b])`, which is polycyclic in `SL_3(Z)`.
  - The polycyclic part maps with finite kernel into the virtually free
    group `Out(F_2) ≅ GL_2(Z)`, so it is virtually cyclic.
  - See `research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md`,
    Sections 3–5. The route `sl3z-incoherent-via-f2-by-free-subgroup` is
    therefore dead.
