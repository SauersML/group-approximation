---
rg: 2
id: deficiency-zero-kervaire-failure-needs-acyclic-complex-and-no-finite-quotient
kind: claim
title: A Kervaire killing failure over a deficiency-zero presentation needs an acyclic presentation complex, a superperfect coefficient group, and no nontrivial finite quotient
distinct_from:
  deficiency-zero-kervaire-failure-yields-whitehead-counterexample: that turns one deficiency-zero killing failure into a Whitehead counterexample and a non-hyperlinear group; this lists necessary conditions on the coefficient presentation, usable as a search filter.
  kervaire-killing-failure-over-deficiency-zero-group-exists: that is the OPEN existence claim; this constrains its witnesses and asserts none exists.
  kervaire-laudenbach-holds-for-hyperlinear: that is injectivity over hyperlinear coefficient groups; this uses it on finite quotients of the coefficient group.
---

**ESTABLISHED** through `deficiency-zero-kervaire-failure-filter-proof`.
Unreviewed. No novelty is claimed; the arguments are elementary.

Let `G = <x_1, ..., x_n | r_1, ..., r_n>` be a balanced finite presentation with
presentation complex `K`, let `w in G * <t>` have exponent sum `+-1` in `t`, and
suppose `G != 1` and `G_w = (G * <t>)/<<w>> = 1`. Then:

1. `H_1(G) = 0`: the `n x n` exponent-sum matrix of the relators has
   determinant `+-1`.
2. `K` is acyclic, and `G` is superperfect: `H_1(G) = H_2(G) = 0`.
3. `G` has no nontrivial finite quotient.
4. Every nontrivial hyperlinear quotient is excluded too, so `G` has no nontrivial
   finite-dimensional unitary representation.

**Use.** Item 3 turns any certified nontrivial finite quotient of `G` into a proof
that no `w` of exponent sum `+-1` kills `G`, whatever its length. So a search for
a deficiency-zero killing failure only needs to consider presentations with no
nontrivial finite quotient, which in particular have trivial abelianization.
