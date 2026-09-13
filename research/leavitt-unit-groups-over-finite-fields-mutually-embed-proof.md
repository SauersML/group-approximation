---
rg: 2
id: leavitt-unit-groups-over-finite-fields-mutually-embed-proof
kind: route
title: Prefix codes lower the arity, the regular representation of F_q lowers the field, and a split corner raises both
target: leavitt-unit-groups-over-finite-fields-mutually-embed
requires: [leavitt-algebras-l-k-1-n-are-simple]
---

Notation. In `L_K(1,m)` write `S[w] = x_(w_1) ... x_(w_l)` and
`T[w] = y_(w_l) ... y_(w_1)` for a word `w` over `{0..m-1}`. For incomparable words
`T[w] S[w'] = 0`, and `T[w] S[w] = 1`. A unital ring homomorphism restricts to an
injective homomorphism of unit groups whenever it is injective. By
`leavitt-algebras-l-k-1-n-are-simple`, a unital homomorphism out of `L_K(1,m)` into a
nonzero ring is injective. Let `q = p^k`.

**(a) `L_(F_q)(1,n)^x -> L_(F_q)(1,2)^x`.** The binary words
`alpha_i = 1^i 0` for `0 <= i <= n-2`, together with `alpha_(n-1) = 1^(n-1)`, form a
complete prefix code. Put `x_i = S[alpha_i]` and `y_i = T[alpha_i]`. Then
`y_i x_j = delta_ij` because the code is prefix, and `sum_i x_i y_i = 1` because it
is complete. The universal property gives a unital homomorphism
`L_(F_q)(1,n) -> L_(F_q)(1,2)`.

**(b) `L_(F_q)(1,2)^x -> L_(F_p)(1,2)^x`.**
1. Let `rho : F_q -> M_k(F_p)` be the regular representation.
2. In `M_k(L_(F_p)(1,2))` the elements `s_i I_k` and `t_i I_k` commute with
   `rho(F_q)`. They satisfy the binary Leavitt relations, so they define a unital
   homomorphism `L_(F_q)(1,2) -> M_k(L_(F_p)(1,2))`.
3. For a complete binary prefix code `beta_1..beta_k` with `k` words,
   `(z_ij) -> sum_(i,j) S[beta_i] z_ij T[beta_j]` is a unital ring isomorphism
   `M_k(L) -> L`. Its inverse is `z -> (T[beta_i] z S[beta_j])`, and
   multiplicativity uses `T[beta_j] S[beta_j'] = delta_(jj')`.
4. Composing gives a unital homomorphism `L_(F_q)(1,2) -> L_(F_p)(1,2)`.

**(c) `L_(F_p)(1,2)^x -> L_(F_q')(1,n')^x`.** Put `A = L_(F_q')(1,n')`, letters
`0..n'-1`, and `e = sum_(i=0)^(n'-2) S[i] T[i]`.
1. Split the first cylinder: list the words
   `w_1..w_(2n'-2) = 00, 01, ..., 0(n'-1), 1, 2, ..., n'-2`. They are pairwise
   incomparable, and `sum_k S[w_k] T[w_k] = e`.
2. Put
   `X_0 = sum_(i=0)^(n'-2) S[w_(i+1)] T[i]` and `Y_0 = sum_i S[i] T[w_(i+1)]`, and
   `X_1 = sum_(i=0)^(n'-2) S[w_(n'+i)] T[i]` and `Y_1 = sum_i S[i] T[w_(n'+i)]`.
3. These lie in `eAe`. Incomparability gives `Y_a X_b = delta_ab e`, and
   `X_0 Y_0 + X_1 Y_1 = sum_k S[w_k] T[w_k] = e`.
4. So they form a binary Leavitt family in the unital `F_p`-algebra `eAe`, whose unit
   is `e != 0`. The universal property gives a unital homomorphism
   `psi : L_(F_p)(1,2) -> eAe`, and it is injective.
5. The map `u -> psi(u) + (1 - e)` is an injective homomorphism of unit groups.

For `n' = 2` the list in step 1 is `00, 01`.

Composing (a), (b) and (c) gives the claimed chain for arbitrary `(q, n)` and
`(q', n')`. ∎
