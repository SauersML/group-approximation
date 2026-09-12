---
rg: 2
id: char-zero-leavitt-congruence-kernel-proof
kind: route
title: Reduce modulo a finite residue field and exhibit a nilpotent congruence unit
target: char-zero-leavitt-unit-groups-have-congruence-kernels
requires: []
---

Write `s_0, s_1, t_0, t_1` for the generators of `L_A(1,2)`, with relations
`t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`.

1. **A faithful-enough module.** Let `X = {0,1}^N` be the set of infinite binary
   words, and `A^(X)` the free `A`-module on `X`. Put `s_i e_x = e_(ix)` and
   `t_i e_(jx) = delta_ij e_x`. These operators satisfy the Leavitt relations,
   because every infinite word starts with `0` or `1`, so they define a
   representation of `L_A(1,2)` on `A^(X)`. The same formulas define a
   representation of `L_F(1,2)` on `F^(X)` for any field `F`.
2. **A finite residue field.** `A` has a maximal ideal `m`. `A/m` is a field that
   is a finitely generated `Z`-algebra, so it is finite by the Nullstellensatz
   over `Z`. Let `F = A/m`, of characteristic `p`, so `p in m`.
3. **Reduction.** The quotient `A -> F` sends the Leavitt relations to the
   Leavitt relations. So it extends to a unital ring homomorphism
   `rho: L_A(1,2) -> L_F(1,2)` fixing the generators, which restricts to a group
   homomorphism `L_A^x -> L_F^x`. Let `N` be its kernel, a normal subgroup.
4. **`N` is proper.** `w = s_0 t_1 + s_1 t_0` satisfies `w^2 = s_0 t_0 + s_1 t_1 = 1`,
   so it is a unit. In the representation over `F`, `rho(w) e_(1x) = e_(0x)`, so
   `rho(w) != 1`, and `w` is not in `N`.
5. **`N` is nontrivial.** Put `z = s_0 t_1`. Then `z^2 = s_0 (t_1 s_0) t_1 = 0`, so
   `u = 1 + p z` is a unit with inverse `1 - p z`. `rho(u) = 1` because `p = 0`
   in `F`, so `u in N`. Also `(u - 1) e_(1x) = p e_(0x)`, which is nonzero because
   `p != 0` in the characteristic-zero domain `A` and `A^(X)` is free. So
   `u != 1`.

Therefore `1 != N != L_A^x`, and `L_A^x` is not simple. QED
