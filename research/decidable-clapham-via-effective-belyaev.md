---
rg: 2
id: decidable-clapham-via-effective-belyaev
kind: route
title: Run Belyaev's construction effectively, replacing Murskii by Birget, to embed a decidable algebra in a decidable finitely presented one
target: decidable-algebras-embed-in-decidable-fp-algebras
requires:
  - belyaev-associative-higman-theorem
  - belyaev-embedding-relations-are-recursive-for-decidable-input
  - semigroup-algebra-of-decidable-semigroup-is-decidable
  - birget-semigroup-embedding-preserves-word-problem
  - belyaev-murskii-semigroups-have-solvable-word-problem
  - belyaev-lemma-one-preserves-word-problem
---

Let `A` be a finitely generated `K`-algebra with solvable word problem, `K` a
decidable field (`F_p`, `Q`, or any field finitely generated over its prime
field with decidable equality). Run Belyaev's construction
(`belyaev-associative-higman-theorem`), tracking the word problem.

1. **Effective data.** By
   `belyaev-embedding-relations-are-recursive-for-decidable-input` the
   enumeration `(a_i)`, the equality set `Y`, the counting functions `f, g`, and
   the pairing functions `n_i, s` are computable, so the special algebra `S`
   and the two semigroups `G` and `H` have recursive defining relations.

2. **Birget replaces Murskii.** Belyaev applies Murskii's theorem to `G` and to
   `H`. By `belyaev-murskii-semigroups-have-solvable-word-problem` both have
   solvable word problem, so `birget-semigroup-embedding-preserves-word-problem`
   gives finitely presented `G_1 ⊇ G` and `H_1 ⊇ H` whose word problems are
   solvable (each reduces to the word problem of `G`, resp. `H`). This is the
   only use Belyaev makes of Murskii, and it is the step that would otherwise
   lose decidability.

3. **The semigroup algebras are decidable.** By
   `semigroup-algebra-of-decidable-semigroup-is-decidable`, `K[G_1]` and
   `K[H_1]` have solvable word problem. Finite direct products of algebras with
   solvable word problem again have solvable word problem (decide each
   coordinate), so `B × S_1`, `S_2 × K[G_1]`, `S_3 × K[H_1]` are decidable at
   each stage where they appear.

4. **Lemma 1 preserves decidability.** The construction adjoins solutions of the
   systems (2), (4), (6) by Belyaev's Lemma 1, and Lemma 3 uses it once more.
   By `belyaev-lemma-one-preserves-word-problem` each application sends an
   algebra with solvable word problem, together with a computable `φ`, to an
   overalgebra with solvable word problem. The maps `φ` here are computable:
   they send generators to explicit elements, and their values `φ[w(ā)]` are
   computed using the solvable word problem of the current algebra.

5. **Termination.** After the three Lemma 1 steps and the `K`-generator
   relations (7), the relation set is the finite union (1)–(7); this is the
   finitely presented envelope of `belyaev-associative-higman-theorem`, and it
   is the terminal algebra of the tower in steps 1–4, so its word problem is the
   composite of the decidable reductions above. Since `K` is decidable, the
   relations (7) among the generators of `K` are decidable as well.

Therefore `A` embeds in a finitely presented `K`-algebra with solvable word
problem, which is the claim `decidable-algebras-embed-in-decidable-fp-algebras`.

**Status.** Two requirements are open holes —
`belyaev-murskii-semigroups-have-solvable-word-problem` and
`belyaev-lemma-one-preserves-word-problem` — so this route does not yet
establish the target. It reduces statement (C) from "recheck the whole Belyaev
construction for decidability" to those two concrete, self-contained lemmas: one
about the word problem of two structured counter-semigroups, one about the word
problem of a single algebra construction. The other three requirements are
established here.
