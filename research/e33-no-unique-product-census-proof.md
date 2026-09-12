---
rg: 2
id: e33-no-unique-product-census-proof
kind: route
title: Normalize both supports to contain the identity and exhaust the no-unique-product condition by SAT
target: e33-no-unique-product-pairs-of-small-radius
requires: []
---

**Unique-product lemma (every field).** Let `alpha, beta` be nonzero in `k[H]`
with supports `A, B`. If some `g in AB` has exactly one expression `g = ab`
with `a in A`, `b in B`, then the coefficient of `g` in `alpha beta` is
`alpha_a beta_b != 0`. So `alpha beta = 0` forces the pair `(A, B)` to have no
uniquely represented product.

**Normalization.** Suppose `(A, B)` has no uniquely represented product, with
`rad_L(A) <= ra` attained at `a_0 in A` and `rad_R(B) <= rb` attained at
`b_0 in B`. Put `A' = a_0^(-1) A` and `B' = B b_0^(-1)`.
- Then `A' B' = a_0^(-1) (AB) b_0^(-1)`, and `a b -> a_0^(-1) a b b_0^(-1)` is
  a bijection on expressions, so every product of `(A', B')` still has at least
  two expressions.
- `1 in A' ⊆ B(ra)` and `1 in B' ⊆ B(rb)`, because `|a_0^(-1) a| <= ra` and
  `|b b_0^(-1)| <= rb`.

So it suffices to exclude pairs with `1 in A ⊆ B(ra)` and `1 in B ⊆ B(rb)`.

**Encoding** (`experiments/zero-divisor-tf/up_sat.py`).
- Balls are enumerated exactly with integer matrix products.
- Unknowns `x_a` (`a in B(ra)`), `y_b` (`b in B(rb)`), with unit clauses for
  the identity in both.
- For each product cell `g` with pairs `P_g`:
  - if `|P_g| = 1`, the clause `NOT x_a OR NOT y_b`;
  - otherwise `z_p <-> x_a AND y_b` and the constraint "the number of true `z_p`
    is 0 or at least 2". Cells with at most 10 pairs use the clauses
    `z_k -> OR_(l != k) z_l`. Larger cells use an exact sequential counter with
    `s_k = [at least one of z_1..z_k]`, `d_k = [at least two]`, both bounded
    above and below, and the clause `s_m -> d_m`.
- The solver is CaDiCaL 1.5.3 through python-sat, single-threaded, on MSI.
- Every SAT model is recomputed exactly (`verify()`): all products of the
  selected sets are counted with integer matrix multiplication.

**Control.** Adjoining `t = diag(-1,-1,1)`, of order 2, the solver answers SAT
at radius one and returns `A = B = {1, t}`, which the exact check confirms has
no uniquely represented product (`runs-up/e33-up-r11-control.json`).

**Runs.** Radii `(2,2)` and `(2,3)` are UNSAT (`runs-up/e33-up-r22.json`,
`runs-up/e33-up-r23.json`). Together with the normalization this proves items
1 and 2 of the claim.

**Inversion.** `(A, B) -> (B^(-1), A^(-1))` reverses every expression
`g = ab` into `g^(-1) = b^(-1) a^(-1)`, so it preserves the no-unique-product
property, and it swaps `rad_L` and `rad_R`. That gives the exchanged-radii
statement. QED
