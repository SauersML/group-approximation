---
rg: 2
id: fg-simple-weak-sofic-linear-sofic-via-near-scalar-covering
kind: route
title: Compactness gives a finite relation set with uniform rank collapse, and the PSL covering argument then kills every PSL weak model, including near-scalar ones
target: fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic
requires: [nst-simple-weakly-sofic-groups-are-psl-approximable, liebeck-shalev-normal-subset-covering, projective-rank-psl-ultraproducts-embed-by-adjoint, simple-group-psl-width-is-finite-field-linear-soficity]
artifacts: [research/artifacts/fg-simple-weak-soficity-finite-field-linear-2026-09-13.md]
---

Section 3 of the artifact. `G = <X | R_inf>` is infinite, finitely generated and simple, and `R_inf` is the set of all
words trivial in `G`. Suppose `G` is not linear sofic over finite fields. We show `G` is not weakly sofic.

1. **Uniform collapse over a finite relation set (3.0).** There are finite `R' <= R_inf` and `delta_0 > 0` with
   `max_(r in R') rk(r(b) - 1) >= delta_0 max_x rk(b_x - 1)` for every tuple `b` in every `GL_m(F_q)`.
   - If not, take tuples violating it for `R_j = {r_1, ..., r_j}` and `delta = 1/j`.
   - Restrict each to a block `Y` of dimension between `p_j` and `2|X| p_j` that carries every word.
   - The normalized-rank ultraproduct receives a homomorphism of `G` that is nontrivial on a fixed generator.
   - By simplicity it is injective, so `G` is linear sofic over finite fields, a contradiction.
2. **Template (3.1).** `x = prod_(j<=J) [u_(x,j), v_(x,j)] q_x` in `F(X)` with `q_x in R_inf`, exact for every tuple.
3. **Weak models (3.2).** If `G` were weakly sofic, NST Theorem 4 would give tuples `a^(i)` in `PSL_(n_i)(q_i)` with
   invariant lengths `l_i <= 1`, `l_i(r(a^(i))) -> 0` for every `r in R_inf`, and `l_i(a^(i)_x) = 1` for nontrivial generators.
4. **Domination (3.3).** Liebeck--Shalev covering gives `l^c <= 4c l_i` where `l_i <= 1/4`. The NST Lipschitz equivalence
   gives `l^pr <= C l^c`. So `G -> prod_U (PSL_(n_i)(q_i), l^pr)` is a homomorphism, hence injective or trivial.
5. **Injective (3.4).** `projective-rank-psl-ultraproducts-embed-by-adjoint` makes `G` linear sofic over finite fields.
   Contradiction.
6. **Trivial, the near-scalar horn (3.5).**
   - Here `P_i = max_x rho(a^(i)_x)` satisfies `1 <= P_i = o(n_i)`, so `n_i -> infinity`.
   - Sections 5.1--5.5 of `simple-group-psl-width-is-finite-field-linear-soficity-proof`: scalar division, localization,
     displacement, and Liebeck--Shalev covering in `PSL(W''')`. They use no finite presentation.
   - Run them with the collapse of item 1 in place of that proof's Section 0, and `R'` in place of `R`.
   - They put every template commutator in `Cons_(4 k_2)(R'(a))`, with `k_2` independent of `i`.
   - By item 2, `1 = l_i(a_x) <= 4 J k_2 max_(r in R') l_i(r(a^(i))) + l_i(q_x(a^(i))) -> 0`. Contradiction.

So `G` is not weakly sofic. Linear soficity over finite fields implies weak soficity (definition bullet on
`simple-group-psl-width-is-finite-field-linear-soficity`), which gives the equivalence.
