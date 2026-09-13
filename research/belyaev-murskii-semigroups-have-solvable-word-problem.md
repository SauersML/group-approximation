---
rg: 2
id: belyaev-murskii-semigroups-have-solvable-word-problem
kind: claim
title: The two semigroups Belyaev feeds to Murskii's theorem have solvable word problem when the input algebra does
distinct_from:
  belyaev-embedding-relations-are-recursive-for-decidable-input: that only makes the defining RELATION SETS of the two semigroups recursive; this asks for their WORD PROBLEM to be solvable, which recursive relations alone do not give (Markov–Post).
  birget-semigroup-embedding-preserves-word-problem: that is the general semigroup theorem, taking a semigroup with solvable word problem to a finitely presented one; this claim is exactly the missing hypothesis needed to apply it to Belyaev's two intermediate semigroups.
---

**OPEN.** In the proof of `belyaev-associative-higman-theorem`, when the input
algebra `A` has solvable word problem and `K` is a decidable field, the two
semigroups fed to Murskii's embedding theorem have solvable word problem:

- `G`, on generators `x', y', z', u', α', β', γ'`, presented by the word
  equalities `Σ` of `S_1` — that is,
  `{x y^i z = x u^{n_i(j)} ε_{ij} z} ∪ {x y^{f(i,j)} z = x u^{s(i,j)} y' z} ∪ {x y^i z = x y^j z : ⟨i,j⟩ ∈ Y}`
  with `ε_{ij} = α'` for `i+j` even and `β'` for `i+j` odd;
- `H`, on generators `ρ, q, τ`, presented by `{ρ q^i τ = ρ q^{g(i,j)} τ}`.

By `belyaev-embedding-relations-are-recursive-for-decidable-input` both relation
sets are recursive. This claim is strictly stronger: a finitely generated
semigroup with a recursive set of defining relations can have undecidable word
problem, so recursiveness of `Σ` and the `g`-relations does not by itself give
solvable word problems.

**Why it is the gap.** With this claim,
`birget-semigroup-embedding-preserves-word-problem` replaces each Murskii
application, producing finitely presented `G_1 ⊇ G` and `H_1 ⊇ H` with solvable
word problem; then `semigroup-algebra-of-decidable-semigroup-is-decidable` gives
`K[G_1]`, `K[H_1]` solvable word problem, which is what the later Lemma 1 steps
consume. See `decidable-clapham-via-effective-belyaev`.

## Attempts

1. **Recursive relations are not enough (why the claim is nontrivial).** A
   finitely generated semigroup with a recursively enumerable — even recursive —
   set of defining relations can have undecidable word problem (Markov, Post).
   So the claim must use the special "single power-block" shape of the relations,
   not just their recursiveness.
2. **The counter shape (route not completed).** Every relation of `G` and `H`
   equates two words each of the form `x [y or u]^power [ε] z` (respectively
   `ρ q^power τ`): one variable power flanked by fixed letters. A word not of
   this shape is a normal form fixed by all relations, and among shaped words a
   relation only rewrites the exponent block through the injective functions
   `n_i, s, f, g`. This suggests a normal form computed by inverting those
   functions, but confluence and termination of the rewriting were not proved,
   and the interaction of `Y`-collapses with the `f`-relations was not settled.
   Establishing it would close this hole.
