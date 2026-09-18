---
rg: 2
id: coset-field-rank-condition-is-lamp-factorization-proof
kind: route
title: Clear left denominators on A and right denominators on B, since nonzero lamp polynomials form a G-stable commutative Ore set
target: coset-field-rank-condition-is-lamp-factorization
requires: []
---

Write `u_g` for the group elements in `R`, so `u_g f = (g . f) u_g` for `f in K`. Let `S = L \ {0}`.
`L` is a Laurent polynomial ring over a field, hence a domain, and `S` is `G`-stable.

**Left clearing.** An element of `R` is a finite sum `sum_g f_g u_g` with `f_g in K`. Choosing a common
denominator `s in S` of the finitely many `f_g` gives `f_g = s^(-1) a_g` with `a_g in L`, so the element is
`s^(-1) (sum_g a_g u_g)` with the bracket in `T`. For a matrix `A` over `R`, take a common denominator `s` of
all coefficients of all entries: `A = s^(-1) A_0` with `A_0` over `T`.

**Right clearing.** Also `f_g u_g = u_g (g^(-1) . f_g)`, so every element of `R` is a finite sum
`sum_g u_g f'_g`. A common denominator `t in S` of the `f'_g` gives `f'_g = b_g t^(-1)` (K is commutative),
so the element is `(sum_g u_g b_g) t^(-1)`, and `u_g b_g in T`. For a matrix `B` over `R`,
`B = B_0 t^(-1)` with `B_0` over `T` and one `t in S`.

**(1) implies (2).** From `AB = I_d` we get `s^(-1) A_0 B_0 t^(-1) = I_d`, and multiplying by the scalar `s`
on the left and `t` on the right gives `A_0 B_0 = s t I_d`, where `s I_d t = st I_d` because `s, t` lie in
the commutative ring `K`. Take `w = st`, which is nonzero because `L` is a domain.

**(2) implies (1).** `w` is invertible in `K`, and `w^(-1) I_d` is a scalar matrix, so
`(w^(-1) A_0) B_0 = w^(-1) w I_d = I_d` over `R`.

**Rank-function corollary.** Suppose `phi : T -> M` is unital and `rk` is a normalized Sylvester matrix
rank function on `M` with `rk(phi(w)) = 1` for every `w in S`. If `A_0 B_0 = w I_d` with inner size `r`,
then `d = rk(phi(w) I_d) = rk(phi(A_0) phi(B_0)) <= rk(phi(A_0)) <= r`, using additivity on diagonal
matrices and the bound of the rank of a `d x r` matrix by `r`. So `r >= d`, and (2), hence (1), fails.

**Identification of T.** `L` is the group algebra of the free abelian group `Z^(H)` with basis `x_c`, and
`G` permutes that basis, so `L semidirect G = k[Z^(H) semidirect G] = k[Z wr_H G]`. Nothing above uses
properties of `G` or `H`, so the reduction applies verbatim to `H x {1,...,m}` and to every field `k`.
