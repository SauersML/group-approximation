---
rg: 2
id: s0-lifts-all-ones-stabilizer-proof
kind: route
title: Row sums in the sequence representation are constant on the all-ones stabilizer
target: s0-lifts-cannot-be-supported-in-the-all-ones-stabilizer
requires: []
---

**The module.** For the monomial `S[a]T[b]`, the value of `S[a]T[b] f` at `omega'` reads
`f` at no point unless `omega' = a eta`, and then at the single point `b eta`. So each
element `x` of `R` acts by a matrix `X = (X_(omega', omega))` with finitely many
nonzero entries in each row, and `(X f)(omega') = sum_omega X_(omega', omega) f(omega)`.
Such row-finite matrices add and compose, and the action respects products.

The relations hold as operators. For `f` in `F` and `eta` in `Omega`:
- `(t_i s_j f)(eta) = (s_j f)(i eta) = delta_ij f(eta)`;
- `(s_0 t_0 f)(0 eta) = f(0 eta)`, while `s_0 t_0 f` vanishes on `[1]`, and symmetrically for `s_1 t_1`. So `s_0 t_0 + s_1 t_1` acts as the identity.

Hence `F` is a left `R`-module, and `x -> X` is a ring map into row-finite matrices.

**(1) Subgroups.**
- If `u 1 = 1` and `v 1 = 1`, then `(uv) 1 = u(v 1) = 1`, and `u^(-1) 1 = u^(-1)(u 1) = 1`. So `H_1` is a subgroup.
- The involution `*` is a ring anti-automorphism of `R`, so it sends units to units with `(u^*)^(-1) = (u^(-1))^*`. Then `H^1 = { u : u^* in H_1 }` is a subgroup as well.
- A Thompson unit `g = sum_i S[r_i]T[d_i]` maps `d_i eta` to `r_i eta`, a bijection of `Omega`, so its matrix is a permutation matrix and `g 1 = 1`.
- `g^* = g^(-1)` also lies in `V`, so `V <= H^1`.

**(2) Constant row sums.** `pi(beta) = sum_(u in supp beta) u`, so
`pi(beta) 1 = sum_u u 1 = |supp beta| 1 = eps(beta) 1`. On the other hand
`(s_0 1)(0 eta) = 1` and `(s_0 1)(1 eta) = 0`. Two elements of `R` that are equal act
equally on `F`, so `pi(beta) != s_0`. No faithfulness of `F` is needed.

**(3) The starred case.** If `supp alpha` lies in `H^1`, then
`pi(alpha)^* = sum_u u^*` has all its terms in `H_1`, so `pi(alpha)^* 1 = eps(alpha) 1`.
Since `t_0^* = s_0`, the equation `pi(alpha) = t_0` would give `s_0 1` constant, which
is false.

**Consistency check.** Exact span computations in
`experiments/nonsofic-certificates/kaplansky-df/sat/dfsat.py` (`span_contains`) find
`s_0` outside the span of `pi(B_r(V))` for `r = 1, ..., 6`, as item 2 requires. By
contrast `s_0` does lie in the span for the atlas charts, whose units leave `H_1`.
