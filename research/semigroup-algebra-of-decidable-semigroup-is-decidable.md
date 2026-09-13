---
rg: 2
id: semigroup-algebra-of-decidable-semigroup-is-decidable
kind: claim
title: The semigroup algebra of a semigroup with solvable word problem over a decidable field has solvable word problem
distinct_from:
  birget-semigroup-embedding-preserves-word-problem: that embeds a semigroup in a finitely presented semigroup keeping the word problem; this passes from a semigroup with solvable word problem to its semigroup ALGEBRA, a different object, and makes no finiteness claim.
  monomial-algebras-embed-in-decidable-fp-algebras: that embeds monomial algebras in finitely presented algebras with solvable word problem; this is the elementary fact its proof uses, that a semigroup algebra inherits decidability from its semigroup.
---

**ESTABLISHED** through `semigroup-algebra-decidable-proof`.

Let `K` be a decidable field and `H` a semigroup (with or without an adjoined
identity `H^1`) with a fixed finite generating set and solvable word problem.
Then the semigroup algebra `K[H]` (respectively `K[H^1]`) has solvable word
problem: it is decidable which finite `K`-combinations of generator words
vanish in `K[H]`.

This is the elementary step used in `monomial-algebras-embed-via-birget-semigroup-embedding`
and in `belyaev-associative-higman-theorem`'s effective form, factored out so
that `decidable-clapham-via-effective-belyaev` can name it. No novelty is
claimed.
