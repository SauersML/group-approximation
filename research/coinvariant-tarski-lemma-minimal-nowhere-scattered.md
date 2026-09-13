---
rg: 2
id: coinvariant-tarski-lemma-minimal-nowhere-scattered
kind: claim
title: For minimal actions on a dimension group whose positive elements divide with order-small remainders, infinite multiples in the type semigroup are properly infinite
distinct_from:
  coinvariant-tarski-lemma-simple-dimension-groups: that treats simple, dense, state-ordered groups, where every action is minimal and the margin comes from order units and states; this allows an arbitrary ideal lattice, replaces states by an order-theoretic divisibility axiom, and takes the margin from minimality of the action.
  opr-mixed-simple-refinement-monoid: that exhibits an abstract simple refinement monoid in which a finite element has a properly infinite multiple; this proves that the type semigroup of a minimal action on an order-divisible dimension group never has such an element.
---

**Lemma.**  Let `(G, G^+)` be a directed partially ordered abelian group with

* (R) `G^+` conical (`G^+ cap -G^+ = 0`) with Riesz refinement;
* (P) `G` unperforated: `n g >= 0` with `n >= 1` gives `g >= 0`;
* (ND) order divisibility: for every `c in G^+` and all integers `N, M >= 1`
  there is `d in G^+` with `N d <= c` and `M (c - N d) <= c`.

Let a group `Gamma` act on `G` by order automorphisms `alpha_t`, minimally: the
only `Gamma`-invariant order ideals of `G` are `0` and `G`.  Let
`Sigma = G^+ / ~` be the type semigroup, where `y ~ y'` means `y = sum c_i` and
`y' = sum alpha_(t_i)(c_i)` for some `c_i in G^+`, `t_i in Gamma` (Rainone,
Definitions 4.6 and 4.8).

Call `theta in Sigma` *infinite* if `theta = theta + eta` with `eta != 0`, and
*properly infinite* if `2 theta <= theta`.  If `x in G^+` is nonzero and
`N[x]` is infinite for some `N >= 1`, then `[x]` is properly infinite.

Consequently every nonzero `theta` with `(k+1) theta <= k theta` for some `k`
is properly infinite, and `Sigma` is purely infinite as soon as it has no
nontrivial state (Tarski, Rainone Theorem 4.11).  This is the condition that
Rainone singles out on page 33 of arXiv:1502.06153 as sufficient for
`(5) => (1)` of his Theorem 4.21.

**Model tests.**

* Every dimension group satisfies (R) and (P).
* (ND) holds in three kinds of groups:
  * simple noncyclic dimension groups, by density and strict ordering by states
    (Effros--Handelman--Shen);
  * `C(X, Z[1/2])` for a Cantor space `X`, pointwise, using dyadic approximations
    of `c/N` from below;
  * `K_0` of every AF algebra with no elementary subquotient
    (`af-k0-order-divisible-iff-no-elementary-subquotient`).
* (ND) fails for `C(X, Z)`: with `c = 1_X` and `N = 2`, `N d <= c` forces
  `d = 0`, and `M = 2` then fails.  So Cantor minimal systems lie outside the
  lemma, and more generally so does every AF algebra with an elementary
  subquotient.
* Minimality binds.  Let `Z` act on `G = Z[1/2] direct_sum Z[1/2]` by doubling
  the first coordinate and fixing the second.  Then `Sigma = {0, infinity} x Z[1/2]^+`.
  The element `[(1,1)] = (infinity, 1)` is infinite, but `2 (infinity, 1) = (infinity, 2)`
  is not `<= (infinity, 1)`.
* The conclusion is not automatic for refinement monoids
  (`opr-mixed-simple-refinement-monoid`).

**Relevance.**  The lemma removes Rainone's almost-unperforation hypothesis
for AF coefficient algebras without elementary subquotients, whatever their
ideal lattice (`nowhere-scattered-af-crossed-products-dichotomy`).  The lemma
of `coinvariant-tarski-lemma-simple-dimension-groups` handled only simple
coefficients, and its attempt notes only lexicographic chains of ideals.  The
division step is exactly what fails at elementary subquotients
(`af-k0-order-divisible-iff-no-elementary-subquotient`).  There the problem
contains Rainone's open question for minimal Cantor systems
(`measure-free-minimal-cantor-action-with-finite-clopen-type`).  The lemma
still reaches that regime when a normal subgroup smooths `K_0` first
(`minimal-normal-cyclic-subgroup-cantor-dichotomy`).

Status: proved in the route below, unreviewed.  Novelty is recorded in the
dichotomy node.
