---
rg: 2
id: sandwich-ring-word-problem-reduces-to-its-group
kind: claim
title: The universal sandwich ring over a group ring has a normal form, so its word problem is decidable when the group's is
distinct_from:
  universal-sandwich-ring-is-finitely-presented-and-injective: that proves injectivity of Z[T] -> U and finite presentation from an external sandwich witness in End(W); this gives an explicit Z-basis of U by irreducible words, which re-proves injectivity and turns the word problem of U into the word problem of T.
  decidable-algebras-embed-in-decidable-fp-algebras: that asks for a decidable finitely presented envelope of an arbitrary decidable algebra; this is one specific one-relator extension of a group ring whose decidability is inherited from the group.
---

Let `T` be a group, `1 != g in T`, and let

    U = Z[T]<p,q> / (p(1-g)q - 1).

Call a word over the alphabet `(T \ {1}) ⊔ {p,q}` **irreducible** when it
has no two adjacent group letters and no subword `p g q`, where `g` is a
single group letter. The irreducible words form a Z-basis of `U`.

Consequently, if `T` is finitely generated with solvable word problem, then
`U` has solvable word problem. More precisely, there is an algorithm that
takes a ring expression in the generators of `T`, their inverses, `p` and
`q`, and decides whether it is `0` in `U`. For every `n`, the same then holds
for equality of matrices in `GL_n(U)`.
