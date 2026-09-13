---
rg: 2
id: relator-width-over-transitive-abelian-extensions-proof
kind: route
title: Lift the quotient covering, then pay for the layer with one commutator against a relator that moves it, or cancel the layer inside template commutators when no relator moves it
target: relator-width-over-transitive-abelian-extensions
requires: [simple-group-relator-width-in-finite-simple-targets, simple-group-psl-width-is-finite-field-linear-soficity, simple-group-classical-width-finite-field-linear-soficity]
---

Notation: `[x, y] = x y x^-1 y^-1`; `N = <<R(a)>>^Q` is the normal closure of the relator values;
`Cons_K = Cons_K^Q(R(a))`. (E1) and (E2) are the two facts of
`simple-group-relator-width-in-finite-simple-targets-proof`, Section 0:
- (E1) every `a_x` lies in `N`, because `G` has no nontrivial finite quotient;
- (E2) in a finite group `H`, every element of a normal closure is a product of at most `|H|` conjugates.

## 1. Lower bound

The projection `Q -> Q/A` maps `Cons_K^Q(R(a))` into `Cons_K^(Q/A)(R(abar))`. So `w_(Q/A)(abar) <= w_Q(a)`.

## 2. Lifting the quotient covering

Let `g in Q` have image in `Cons_K^(Q/A)(R(abar))`. Lift each conjugator to `Q`. The product of the
lifted conjugates of the `r(a)^(+-1)` lies in `Cons_K` and has the same image as `g`. So `g = p · alpha`
with `p in Cons_K` and `alpha in A`.

## 3. Case (a): some relator value acts nontrivially on `A`

Let `h = r*(a)` and `beta_0 in A` with `h beta_0 h^-1 != beta_0`.
- `gamma_0 := [h, beta_0] = h · (beta_0 h^-1 beta_0^-1)` is `h` times a conjugate of `h^-1`. So
  `gamma_0 in Cons_2`. Since `A` is normal, `gamma_0 in A`, and `gamma_0 != 1`.
- By transitivity, every `alpha in A \ {1}` equals `g gamma_0 g^-1` for some `g in Q`. Conjugating both
  factors gives `alpha in Cons_2`.
- By Section 2, `a_x = p_x alpha_x` with `p_x in Cons_K` and `alpha_x in A`. So `a_x in Cons_(K+2)`.

## 4. Case (b): every relator value centralizes `A`

- `C := C_Q(A)` is normal and contains every `r(a)`, so `N <= C`. By (E1), every `a_x` lies in `N`, so
  every word `u(a)` lies in `N`.
- Let `u, v` be template words. `u(abar)` is a product of at most `L` factors `abar_y^(+-1)`, each in
  `Cons_K^(Q/A)(R(abar))`. So `u(abar) in Cons_(LK)^(Q/A)(R(abar))`, and by Section 2, `u(a) = p alpha`
  with `p in Cons_(LK)` and `alpha in A`.
- `p in Cons_(LK) <= N <= C` and `v(a) in N <= C` both commute with `alpha`. Hence
  ```text
  [u(a), v(a)] = p alpha v(a) alpha^-1 p^-1 v(a)^-1 = p v(a) p^-1 v(a)^-1 = [p, v(a)] .
  ```
- `[p, v(a)] = p · (v(a) p^-1 v(a)^-1)` lies in `Cons_(2LK)`.
- By the template, `a_x = prod_(j <= J) [u_(x,j)(a), v_(x,j)(a)] · n_x(a) in Cons_(2JLK + J')`.

Sections 3 and 4 give `w_Q(a) <= max(K + 2, 2JLK + J')`. No constant depends on `Q` or `A`.

## 5. Corollaries

1. **`ASL_n(q)`.** Let `Q = F_q^n x| SL_n(q)` with `n >= 2`, and `A = F_q^n`. Conjugation by `(0, g)`
   acts on `A` as `g`, and `SL_n(q)` is transitive on nonzero vectors. `Q/A = SL_n(q)`.
   - *Bounded.* If `G` is not linear sofic over finite fields, item (ii) of
     `simple-group-psl-width-is-finite-field-linear-soficity` gives `K(G)` with
     `w_(SL_n(q))(abar) <= K(G)` for all `n`, `q`, `abar`. Theorem A gives
     `w_Q(a) <= max(K(G) + 2, 2JLK(G) + J')`.
   - *Unbounded.* If `G` is linear sofic over finite fields, (ii) fails, so there are tuples `abar` over
     `SL_n(q)` with unbounded width. Their split lifts `(0, abar_x)` have at least the same width by
     Section 1.
   - *No weak models under (i).* For a bi-invariant length `l`, bounded width `K` gives
     `l(a_x) <= K max_r l(r(a))`, as in part (C) of `simple-group-relator-width-in-finite-simple-targets`.
2. **`ASp_(2m)(q)`.** Every nonzero vector lies in a hyperbolic pair, and `Sp_(2m)(q)` is transitive on
   hyperbolic pairs (Witt), so it is transitive on nonzero vectors.
   - When `PSp_(2m)(q)` is simple, item `Q_0 = Sp_n(q)`, `Z_0 = 1` of
     `simple-group-classical-width-finite-field-linear-soficity` bounds the quotient width under (i).
   - The finitely many non-simple cases `Sp_4(2)` and `Sp_2(q) = SL_2(q)` are covered by (E2) and by
     item 1 respectively.
3. **Non-split extensions.** Sections 1 to 4 use only that `A` is an abelian normal subgroup on which `Q`
   is transitive. No complement is used.

## 6. What does not transfer

- **Adjoint layers.** For `A = sl_n(q)` under `SL_n(q)`, conjugacy classes in `A` are graded by rank.
  `[r(a), beta]` ranges over `(Ad_(rbar) - 1) sl_n(q)`, whose elements have rank at most
  `2 rk(rbar - 1)`. When all relator tops are near-scalar, one commutator covers only a small-rank part
  of the layer, and Section 3 fails. `simple-group-width-over-congruence-targets` treats that case.
- **Many copies of the natural module.** `(F_q^n)^m x| SL_n(q)` has orbits graded by rank in the
  `n x m` matrices. Section 3 fails in the same way. It is not treated here.
