---
rg: 2
id: induced-cantor-action-type-semigroup-matches-subgroup-proof
kind: route
title: Coset representatives split the induced space into copies of X, and only elements of H move the identity copy into itself
target: induced-cantor-action-type-semigroup-matches-subgroup
requires: []
---

Fix coset representatives `t_1 = e, t_2, ..., t_k` for `G/H`.  Write
`[g, x]` for the class of `(g, x)`.  Every class has a unique representative
`[t_j, x]`, so `Y = t_1 x X ⊔ ... ⊔ t_k x X` is `k` copies of `X`: a Cantor
space.  For `g in G` and `j` write `g t_j = t_(j') h` with `h in H`; then
`g [t_j, x] = [t_(j'), h x]`.

**Freeness.**  `g [t_j, x] = [t_j, x]` holds exactly when `j' = j` and
`h x = x`, where `h = t_j^(-1) g t_j`.  So the stabilizer of `[t_j, x]` is
`t_j Stab_H(x) t_j^(-1)`.  All are trivial if and only if the `H`-action is
free.

**Minimality.**  For `h in H` and any `i`, the element `g = t_i h t_j^(-1)`
sends `[t_j, x]` to `[t_i, h x]`.  So the `G`-orbit of `[t_j, x]` is
`⊔_i t_i x (H x)`.  It is dense in `Y` for every point if and only if every
`H`-orbit is dense in `X`.

**Type semigroups.**  Recall that `S(X, H)` is the quotient of the monoid of
clopen subsets of `X x N` (finitely many levels) by equidecomposability, with
pieces moved by elements of `H` and levels permuted freely.

* *The map.*  Send a clopen `E ⊆ X x N` to `{e} x E ⊆ Y x N`.  An
  `H`-equidecomposition of `E` with `E'` is a `G`-equidecomposition of
  `{e} x E` with `{e} x E'`, using the same elements.  So
  `phi: S(X, H) -> S(Y, G)` is a well-defined monoid homomorphism.
* *Surjective.*  A clopen of `Y x N` is a finite disjoint union of sets
  `t_j x E_j` with `E_j ⊆ X x N` clopen and in pairwise distinct levels.
  Since `t_j^(-1) [t_j, x] = [e, x]`, the class of `t_j x E_j` equals the
  class of `{e} x E_j`.  Moving the pieces to fresh levels shows that the
  whole set has class `sum_j phi([E_j])`.
* *Injective.*  Let `{e} x E` and `{e} x E'` be `G`-equidecomposable via
  pieces `P_i ⊆ E` and elements `g_i`.  A piece is nonempty, and
  `g_i [e, x] = [g_i, x]` lies in the identity copy `t_1 x X` only when
  `g_i in H`.  So every `g_i` lies in `H` and acts on the `X`-coordinate by
  itself.  The same pieces and elements give an `H`-equidecomposition of `E`
  with `E'`.

So `phi` is an isomorphism of monoids.  It sends `[1_X]` to `[{e} x X]`, and
`[1_Y] = sum_j [t_j x X] = k [1_X]`.  Almost unperforation is a property of
the monoid alone, so it transfers in both directions.

**Measures.**  A `G`-invariant probability `nu` on `Y` gives the `H`-invariant
measure `k nu(e x -)` on `X`.  Conversely an `H`-invariant `m` gives
`nu(t_j x A) = m(A)/k`, which is `G`-invariant by the formula for
`g [t_j, x]`.  QED.
