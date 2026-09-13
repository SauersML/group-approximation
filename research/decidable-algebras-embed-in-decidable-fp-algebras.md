---
rg: 2
id: decidable-algebras-embed-in-decidable-fp-algebras
kind: claim
title: Every finitely generated associative algebra with solvable word problem embeds in a finitely presented algebra with solvable word problem
distinct_from:
  clapham-fp-embedding-preserves-word-problem: that is Clapham's theorem for groups; this is the associative-algebra analogue, which no source in this graph states with the decidability clause.
  algebra-boone-higman-conjecture: that asks for a finitely presented simple envelope; this asks only for a finitely presented overalgebra with solvable word problem, which the root implies.
---

**OPEN.** Let `K` be a computable field. Every finitely generated associative
`K`-algebra with solvable word problem embeds in a finitely presented `K`-algebra
with solvable word problem.

This is the algebra form of Clapham's theorem for groups
(`clapham-fp-embedding-preserves-word-problem`).

## Where it sits

- **Necessary for the root.** `algebra-boone-higman-conjecture` implies it, via route
  `algebra-bh-implies-decidable-fp-overalgebras`: finitely presented simple algebras
  have solvable word problem.
- **Half of the root.** By `simple-ln-completion-premise-is-equivalent-to-algebra-bh`
  (part 2), the root is equivalent to this claim together with Boone--Higman for
  finitely presented algebras with solvable word problem.
- **Benchmark.** The monomial algebras `A_X = K<x,y>/(x y^n x : n in X)`, with `X`
  decidable of high complexity, are the hard inputs of
  `no-fp-simple-algebra-hosts-every-decidable-algebra`. They are also the natural
  test inputs here.

## Literature

- **Associative Higman theorem (secondary only).** The Gröbner--Shirshov survey of
  Bokut and Chen (arXiv:1303.5366, text extracted from the arXiv PDF) says: "The
  problem [21] whether an analogue of the Higman embedding theorem is valid for Lie
  algebras is still open. For associative algebras a similar problem [21] was solved
  positively by V. Y. Belyaev [10]." Reference [10] is V. Ya. Belyaev, *Subrings of
  finitely presented associative rings*, Algebra i Logika. The survey states the
  recursively-presented-into-finitely-presented embedding. It does not state that
  solvability of the word problem is preserved. Belyaev's paper was not read.
- **Semigroups (not read).** J.-C. Birget, *Time-complexity of the word problem for
  semigroups and the Higman embedding theorem*, Internat. J. Algebra Comput. 8 (1998),
  DOI 10.1142/S0218196798000132. The title was found through Crossref, but the World
  Scientific PDF was not accessible, so no statement from it is used.

## Attempts

1. **Direct finite complete rewriting system for `A_X`** (2026-09-13). Adjoin head letters
   and a trigger rule `x y -> x h_0 y` that runs a total decider for `X` on the `y`-block
   and produces `0` on acceptance. Acceptance kills exactly the words containing
   `x y^n x`, `n in X`. *Unclear, not landed.* The simulation keeps the `x, y`
   skeleton, so distinct basis words keep distinct normal forms. The difficulty is
   global confluence and termination on arbitrary words over the enlarged alphabet:
   several heads, heads meeting the trigger (the overlap `h_q x y`), and heads at the
   end of a word.
2. **Through contracted semigroup algebras.** An embedding of the monoid-with-zero
   `M_X` into a finitely presented monoid-with-zero with solvable word problem, with
   zero preserved, gives (C) for `A_X`, because contracted semigroup algebras of
   monoids with zero preserve such embeddings. *Blocked on sources:* a semigroup
   theorem that preserves the zero element was not found.
