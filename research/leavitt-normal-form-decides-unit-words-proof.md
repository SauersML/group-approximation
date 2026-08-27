---
rg: 2
id: leavitt-normal-form-decides-unit-words-proof
kind: route
title: Reduce Leavitt monomials and then use wreath normal forms
target: binary-leavitt-unit-word-problem-decidable
requires:
  - binary-leavitt-all-ranks-full-mf-radical
---

Orient the binary Leavitt relations as

```text
t_i s_j -> delta_(i,j),
s_1 t_1 -> 1+s_0 t_0.                                  (LNF1)
```

The standard Diamond-lemma normal form has basis

```text
s_alpha t_beta
```

where `alpha,beta` are finite binary words and they do not both end in the
chosen special letter `1`, together with the empty-word conventions.  The
only overlap ambiguities in `(LNF1)` are `t_i s_1 t_1` and `s_1 t_1 s_j`.
Both reductions agree; in the two off-diagonal cases the duplicate term
cancels because the coefficient field is `F_2`.  A length-lexicographic
monomial order makes the system terminating.  Thus finite sums reduce
effectively to unique finite `F_2`-linear combinations of the displayed
basis, and equality in `R` is decidable.

Choose the explicit finite generating set of `U` obtained from its
identification with the finitely generated elementary group in
`binary-leavitt-all-ranks-full-mf-radical`.  Store each generator and its
inverse as a ring expression.  A group word is trivial exactly when the
product of these expressions reduces to the ring identity, proving the first
assertion.

For `U^(G) semidirectProduct G`, scan a word while maintaining its actor
coordinate and a finite dictionary from `G` to `U`.  Actor multiplication
moves dictionary addresses; decidability in `G` combines equal addresses,
and decidability in `U` removes identity values.  The resulting element is
trivial exactly when the actor is trivial and the dictionary is empty.
Finite products and finite permutation extensions add only finite tuples and
a finite permutation coordinate, proving the remaining assertions.
