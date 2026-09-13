---
rg: 2
id: dimension-group-divisible-iff-no-integer-subquotient
kind: claim
title: A countable dimension group divides with order-small remainders exactly when no order-subquotient is the ordered integers
distinct_from:
  af-k0-order-divisible-iff-no-elementary-subquotient: that characterizes order divisibility of K_0 of an AF algebra through elementary subquotients of the algebra; this is the purely order-theoretic form, which applies to K_0 of any C*-algebra whose K_0 is a countable dimension group.
---

**Theorem.**  Let `G` be a countable dimension group.  The following are
equivalent.

1. (ND): for every `c in G^+` and `N, M >= 1` there is `d in G^+` with
   `N d <= c` and `M(c - N d) <= c`.
2. There are no order ideals `I subset J` of `G` such that `J/I`, with positive
   cone the image of `J^+`, is order-isomorphic to `(Z, N)`.

So the divisibility axiom of `coinvariant-tarski-lemma-minimal-nowhere-scattered`
fails exactly at discrete one-dimensional layers of the ideal lattice.

**Model tests.**

* `C(X, Z)` for a Cantor space `X` fails 2: `J = C(X, Z)`, `I` the functions
  vanishing at a point.
* `C(X, Z + theta Z)` with pointwise order (`theta` irrational) satisfies 2.
* A lexicographic product `Z x_lex H` with `H` a noncyclic simple dimension
  group fails 2: its quotient by the ideal `0 x H` is `(Z, N)`.
* `H x_lex Z` fails 2: the ideal `0 x Z` is `(Z, N)`.
