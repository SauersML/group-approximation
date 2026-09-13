---
rg: 2
id: birget-semigroup-embedding-preserves-word-problem
kind: claim
title: Every finitely generated semigroup with solvable word problem embeds in a finitely presented semigroup with solvable word problem
distinct_from:
  clapham-fp-embedding-preserves-word-problem: that is the group theorem, with a group envelope; this is the semigroup theorem, whose envelope is only a semigroup, so an identity or a zero of the input need not stay an identity or a zero in the envelope.
---

Every finitely generated semigroup `S` with solvable word problem embeds in a
finitely presented semigroup `H` with solvable word problem. More precisely, the
word problem of `H` reduces to that of `S` by a conjunctive linear-time reduction.

J.-C. Birget, *Time-complexity of the word problem for semigroups and the Higman
embedding theorem*, Internat. J. Algebra Comput. 8 (1998), no. 2, 235--294,
DOI 10.1142/S0218196798000132. From the author's abstract, as deposited with
Crossref (`api.crossref.org/works/10.1142/S0218196798000132`, fetched 2026-09-13):

> Let S be a finitely generated semigroup whose word problem has nondeterministic
> time complexity T (where T is a function on the positive integers which is
> superadditive, i.e. T(n+m) ≥T(n)+T(m)). Then S can be embedded in a finitely
> presented semigroup H in which the derivation distance between any two
> equivalent words x and y (and hence the isoperimetric function) is
> O(T(∣x∣+∣y∣)²). Moreover, there is a conjunctive linear-time reduction from the
> word problem of H to the word problem of S, so the word problems of S and H
> have the same nondeterministic time complexity (and also the same deterministic
> time complexity).

## Why the abstract gives the decidability form

Let `S` have solvable word problem, decided by an algorithm that takes `t(l)`
steps on inputs of length `l`. Then `t` is recursive, because the algorithm halts
on the finitely many inputs of each length. The function
`T(n) = n (1 + max_{k <= n} t(k))` is superadditive and bounds the running time of
a deterministic, hence nondeterministic, algorithm for the word problem of `S`.

The theorem then gives `H`. A conjunctive reduction sends a pair of words over
`H` to finitely many pairs of words over `S`, all of which are equal in `S`
exactly when the given pair is equal in `H`. So the word problem of `H` is
decidable.

## Verification status

- **Statement.** Taken from the author's own abstract, quoted above. The World
  Scientific PDF endpoints returned the paywall HTML page, so the formal theorem
  and its proof were not read.
- **Extra hypotheses.** If the formal theorem asks more of `T` than the abstract
  says (for example time-constructibility), the argument above still applies:
  it uses `T` only as an upper bound, and it can be enlarged to meet the usual
  regularity conditions. This was not checked against the paper.
