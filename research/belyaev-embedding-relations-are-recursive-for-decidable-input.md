---
rg: 2
id: belyaev-embedding-relations-are-recursive-for-decidable-input
kind: claim
title: For an input algebra with solvable word problem over a decidable field, Belyaev's construction has recursive coordinating data and recursive defining relations at every stage
distinct_from:
  belyaev-associative-higman-theorem: that produces the finitely presented envelope from a recursively enumerable presentation; this says that, when the input has solvable word problem, the enumeration, the equality set Y, the counting function f, and the relation sets of the algebra S and of the two Murskii semigroups G and H are all recursive rather than merely recursively enumerable.
  belyaev-murskii-semigroups-have-solvable-word-problem: that asks for solvable WORD PROBLEM of the two semigroups; this only makes their defining RELATION SETS recursive, which is strictly weaker (Markov–Post).
  decidable-algebras-embed-in-decidable-fp-algebras: that is the full statement (C); this is one effective ingredient of the reduction to it.
---

**ESTABLISHED** through `belyaev-embedding-relations-recursive-proof`.

Let `K` be a decidable field (equality and the field operations are computable;
`F_p` and `Q` qualify, as does any field finitely generated over its prime
field with decidable equality). Let `A` be a finitely generated associative
`K`-algebra with solvable word problem. Then in Belyaev's construction
(`belyaev-associative-higman-theorem`):

1. there is a computable enumeration `a_1, a_2, …` of representatives of the
   elements of `A`, each element represented infinitely often;
2. the set `Y = {⟨i,j⟩ : a_i = a_j in A}` is decidable;
3. the counting function `f` with `a_i + a_j = a_{f(i,j)}` is computable;
4. consequently the special algebra `S`, the semigroup `G` carrying the word
   equalities of `S_1`, and the counting semigroup `H` each have a **recursive**
   set of defining relations.

This isolates the two places where recursiveness of relations is not enough:
Murskii's theorem tolerates recursively enumerable relations, but its
replacement `birget-semigroup-embedding-preserves-word-problem` needs the
semigroups `G` and `H` to have solvable word problem, and Lemma 1 must preserve
the word problem. Both are recorded as open holes.

No novelty is claimed; the content is the effective reading of a published
construction.
