---
rg: 2
id: fn-free-action-via-profinite-diagonal-certificate
kind: route
title: Extend diagonally by the profinite completion along the chain, carry the certificate up, and use Tarski on the measure-free minimal extension
target: free-minimal-fn-cantor-action-not-almost-unperforated
requires: [fn-cantor-action-with-covariant-stateless-certificate, profinite-diagonal-cantor-type-is-transfer-limit, kmp-tarski-theorem-preordered-monoids]
---

Let `X`, `N_j`, `M`, `mu_j` and `A` witness
`fn-cantor-action-with-covariant-stateless-certificate`.  Let `K = lim F_n/N_j`
and `Y = X x K` with the diagonal action.  By items 1–3 of
`profinite-diagonal-cantor-type-is-transfer-limit`, `Y` is a Cantor space, and
the action is free and minimal with no invariant Borel probability measure.
By item 5 there is an invariant finitely additive `nu : Clopen(Y) -> M` with
`nu(A x K) = mu_0(A)`.

`nu` extends additively to clopens of `Y x N` by summing over levels.  It is
constant on equidecomposition classes, so it gives a monoid homomorphism
`S(Y, F_n) -> M`, which preserves the algebraic order.

Let `x = [A x K]`.  Then `A` is nonempty, since `2 mu_0(∅) = 0 <= 0`.  So
`x != 0`, because equidecomposition preserves nonemptiness.

**`x` is paradoxical.**  Suppose `sigma : S(Y, F_n) -> [0, infinity]` is a
state with `sigma(x) = 1`.
* By minimality finitely many translates of `A x K` cover `Y`.  Shrinking
  them to disjoint pieces gives `[1_Y] <= m x`.  Since `x <= [1_Y]`, this
  gives `1 <= sigma([1_Y]) <= m`.
* Then `E -> sigma([E]) / sigma([1_Y])` is an invariant finitely additive
  probability on `Clopen(Y)`.
* By compactness it is countably additive on that algebra, so it extends to
  an invariant Borel probability measure, a contradiction.

By `kmp-tarski-theorem-preordered-monoids`, `(k+1) x <= k x` for some `k >= 1`.
Adding `i x` to both sides and iterating gives `(k+i) x <= k x` for all
`i >= 0`, so `(k+1)(2x) = (2k+2) x <= k x`.

**Failure of almost unperforation.**  If `S(Y, F_n)` were almost
unperforated, then `2x <= x`, i.e. `2x + z = x` for some type `z`.  Applying
`nu` gives `2 mu_0(A) + nu(z) = mu_0(A)`, so `2 mu_0(A) <= mu_0(A)`.  This
contradicts the hypothesis.  So `F_n` acts freely and minimally on the Cantor
space `Y`, and `S(Y, F_n)` is not almost unperforated.
