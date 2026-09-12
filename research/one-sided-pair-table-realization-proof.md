---
rg: 2
id: one-sided-pair-table-realization-proof
kind: route
title: Push coefficients forward along the realization and compare the two products
target: one-sided-inverse-pairs-transfer-to-table-realizations
requires: []
---

## Theorem

`phi_*` is the `k`-linear map `k[C] -> k[H]` with `[g] -> [phi(g)]`. Expand
`alpha beta` as a sum over pairs, then push forward:

    phi_*(alpha beta) = sum_(a,b) x_a y_b [phi(ab)] = sum_(a,b) x_a y_b [phi(a)] [phi(b)] = phi_* alpha . phi_* beta.

The first equality holds even when `phi` merges products. It is linearity of
`phi_*` applied to the pair expansion, and grouping pairs by their product in `G`
does not change the pushed-forward sum. The second equality is multiplicativity
on `A x B`. Since `alpha beta = 1` and `phi(1) = 1`, the product is `1`. The
same computation on `B x A` gives `phi_* beta . phi_* alpha = phi_*(beta alpha)`,
and subtracting `[1] = phi_*[1]` gives the stated difference.

`beta alpha - 1` is nonzero and supported in `BA u {1}`. If `phi` is injective
there, `phi_*` sends distinct cells to distinct basis elements, so
`phi_*(beta alpha - 1) != 0`.

## Corollary 1

For finite `H`, `k[H]` is finite-dimensional. A one-sided inverse in a
finite-dimensional algebra is two-sided: left multiplication by `phi_* alpha` is
surjective, hence injective, and `phi_* alpha (phi_* beta phi_* alpha - 1) = 0`.
So `phi_*(beta alpha - 1) = 0`. The coefficient of `[h]` in it is the sum of
`c_g` over the fibre of `h`.

Realizations `phi_1, ..., phi_m` into finite groups `H_i` give the realization
`g -> (phi_1(g), ..., phi_m(g))` into `prod H_i`. Its fibres are the
intersections of fibres.

## Corollary 2

The relators make `g -> x_g` multiplicative on `A x B` and `B x A`, and `x_1 = 1`.
The homomorphism `U(A, B) -> G` exists because every relator holds in `G`, and it
sends `x_g` to `g`. So the canonical map is injective on `C`, and the theorem
transfers a pair from `G` to `U(A, B)`. The converse transfer is along that
homomorphism, which is injective on `C`. The last sentence is Corollary 1 for
`H = U(A, B)` composed with a finite quotient.

## Corollary 3

Here `C = B_(2r)`, and the two relator families coincide.
- **Map `U(A, B) -> G_(4r)`.** For each `g` fix a geodesic word `w_g`, of length
  `|g| <= 2r`. Any two words of length at most `2r` for the same `g` differ by a
  trivial word of length at most `4r`, so they are equal in `G_(4r)`. Each relator
  `x_a x_b x_(ab)^(-1)`, with `a, b in B_r`, goes to `w_a w_b w_(ab)^(-1)`. That word
  is trivial and has length at most `r + r + 2r = 4r`.
- **Map `G_(4r) -> U(A, B)`.** Send each letter `s` to `x_s`. By induction on
  length, a word of length at most `r` representing `g` maps to `x_g`: if it is
  `u s` with `u` representing `g'`, then `g'` and `s` lie in `B_r`, so
  `x_(g') x_s = x_(g' s)` is a relator. Now let `w` be a trivial word of length at
  most `4r`. Cut it into four words of length at most `r`, representing
  `g_1, g_2, g_3, g_4` with `g_1 g_2 g_3 g_4 = 1`. In `U(A, B)`:

      x_(g_1) x_(g_2) = x_(g_1 g_2) = x_(g_4^(-1) g_3^(-1)) = x_(g_4^(-1)) x_(g_3^(-1)),

  so the image of `w` is `x_(g_4^(-1)) x_(g_3^(-1)) x_(g_3) x_(g_4)`. Both
  `x_(g_3^(-1)) x_(g_3) = x_1 = 1` and `x_(g_4^(-1)) x_(g_4) = 1` are relators,
  so `w` maps to `1`.
- **The composites are identities.** A letter `s` goes to `w_s`, which represents
  `s` and has length at most `2r`, so it equals `s` in `G_(4r)`. A generator
  `x_g` goes to the letters of `w_g = u v`, with `|u|, |v| <= r` representing
  `g_1, g_2`. These multiply to `x_(g_1) x_(g_2) = x_g`.

Under the isomorphism, the cells `B_(2r)` go to the elements of the ball of
radius `2r` in `G_(4r)`. That ball maps bijectively onto `B_(2r)` in `G`,
because two words of length at most `2r` with the same value in `G` are already
equal in `G_(4r)`. If `<X>` has a presentation with relators of length at most
`4r`, those relators hold in `G_(4r)`. Then `G_(4r) -> <X>` is an isomorphism.
