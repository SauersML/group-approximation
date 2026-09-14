---
rg: 2
id: klyachko-kl-holds-when-all-coefficients-have-infinite-order
kind: claim
title: Unimodular equations inject their coefficient group whenever every coefficient has infinite order
distinct_from:
  klyachko-kl-holds-for-torsion-free: that records the torsion-free case at second hand; this is the statement Klyachko actually proves, read from the published paper, and it allows torsion in the group as long as the coefficients occurring in the equation have infinite order.
  kl-sign-index-two-infinite-order-loops-inject: that needs infinite order only at the two sign-change coefficients but restricts to exactly two sign changes; this allows every shape at exponent sum one but needs every coefficient of infinite order.
  kl-holds-over-central-extensions-of-torsion-free-groups: that allows arbitrary central torsion in the coefficients; this allows arbitrary torsion in the group away from the coefficients.
artifacts:
  - research/artifacts/hl-kl-torsion-pins-2026-09-13.md
---

Let `G` be any group and `w in G * <t>` with `deg_t(w) = ±1`. Write a
cyclically reduced conjugate of `w` in normal form

    w' = g_1 t^(k_1) g_2 t^(k_2) ... g_n t^(k_n),     g_i in G \ {1},  k_i != 0.

If every `g_i` has infinite order in `G`, then

    G  -->  (G * <t>)/<<w>>

is injective.

The coefficients are well defined up to cyclic permutation and conjugation in
`G`, which preserve orders, so the hypothesis does not depend on the chosen
cyclically reduced form.

This is Klyachko's Theorem A / Theorem 4 (Comm. Algebra 21 (1993), p. 2556 and
p. 2573), whose proof ends "hence the natural map G ---> K is a monomorphism".
Torsion-freeness of `G` is the special case he states after it.

## What it changes

- **Where torsion enters Klyachko's proof.** Only through relative freeness of
  the coefficient subgroups `gp(a_i, P) = <a_i> * P`; the car-crash count itself
  uses no algebra. See section 1 of the artifact.
- **A screen for unimodular violations.** Suppose `(G, w)` violates
  `kervaire-laudenbach-nonsingular-conjecture` with `deg_t(w) = ±1`. Then some
  coefficient of every cyclically reduced conjugate of `w` has finite order.
  The same holds after any substitution `t -> x t y` with `x, y in G`, since that
  is an automorphism of `G * <t>` fixing `G` and so preserves injectivity. Under
  it the sign-change coefficients change only by conjugation in `G`
  (`t a t^(-1) -> x t (y a y^(-1)) t^(-1) x^(-1)`), so their orders are
  invariant. A violation needs a finite-order sign-change coefficient, or, for
  every choice of `x, y`, a same-sign coefficient `y a x` or `x^(-1) a y^(-1)`
  that is nontrivial and of finite order. (A same-sign coefficient that becomes
  `1` disappears from the normal form and imposes nothing.)
- **It does not reach torsion groups.** Over a group of finite exponent every
  coefficient has finite order and nothing is gained.

**ESTABLISHED** as a citation import through
`klyachko-infinite-order-coefficients-citation`. Not independently reviewed.
