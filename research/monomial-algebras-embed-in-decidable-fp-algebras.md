---
rg: 2
id: monomial-algebras-embed-in-decidable-fp-algebras
kind: claim
title: Every finitely generated monomial algebra with solvable word problem embeds in a finitely presented algebra with solvable word problem
distinct_from:
  decidable-algebras-embed-in-decidable-fp-algebras: that is the statement for every finitely generated algebra; this is the case of monomial algebras, and more generally of contracted algebras of monoids with zero, whose multiplication is monomial up to zero.
  birget-semigroup-embedding-preserves-word-problem: that embeds semigroups in semigroups; this embeds algebras, and it has to remove the zero of the input monoid inside the semigroup algebra of the envelope, without passing to a quotient.
  no-fp-simple-algebra-hosts-every-decidable-algebra: that says no class of hosts with one recursive time bound contains every A_X; this gives each A_X its own finitely presented host with solvable word problem, and that host's complexity grows with X.
---

**ESTABLISHED** through `monomial-algebras-embed-via-birget-semigroup-embedding`,
a complete proof from `birget-semigroup-embedding-preserves-word-problem`.

Let `K` be a computable field. An algebra has *solvable word problem* when, for
some (equivalently, every) finite generating set, it is decidable which
noncommutative polynomials over `K` in the generators vanish in the algebra.

1. **Monomial algebras.** Let `F` be a set of words in `x_1, ..., x_k`. If
   `A = K<x_1, ..., x_k>/(F)` has solvable word problem, then `A` embeds, by a
   unital homomorphism, in a finitely presented `K`-algebra with solvable word
   problem.
2. **Contracted monoid algebras.** Let `M` be a finitely generated monoid with a
   zero `z` and with solvable word problem, and let `K_0[M] = K[M]/Kz`. Then
   `K_0[M]` embeds in a finitely presented `K`-algebra `B` with solvable word
   problem.
   - The embedding sends `1` to an idempotent of `B`.
   - It can be chosen unital whenever `K_0[M]` has a unital homomorphism to `K`.

## Consequence for the benchmark

Take any decidable `X`, and put `A_X = K<x,y>/(x y^n x : n in X)`.
- **The overalgebra.** `A_X` has a finitely presented overalgebra with solvable
  word problem. So statement (C) of `decidable-algebras-embed-in-decidable-fp-algebras`
  holds on its benchmark inputs.
- **The explicit map.** Let `phi` embed the monoid with zero of `A_X` in a
  finitely presented semigroup `H`, and let `e = phi(z)`. Then `x -> phi(x) - e`,
  `y -> phi(y) - e` extends to a unital embedding of `A_X` in the semigroup
  algebra `K[H^1]`.

There is no conflict with `no-fp-simple-algebra-hosts-every-decidable-algebra`.
The host depends on `X`, and its word problem is as hard as membership in `X`.

## Scope

- **General algebras are not covered.** A general finitely generated algebra has
  no basis that is closed under multiplication up to zero, so it is not a
  contracted monoid algebra. The remaining gap is recorded in
  `decidable-algebras-embed-in-decidable-fp-algebras`.
- **Part 2 without a character.** There the embedding found here is not unital.
