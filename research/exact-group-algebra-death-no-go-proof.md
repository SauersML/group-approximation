---
rg: 2
id: exact-group-algebra-death-no-go-proof
kind: route
title: Enumerate the equality classes of the mark support and decide HALT
target: exact-group-algebra-death-cannot-code-nonhalting
requires:
  - word-problem-of-finite-presentation-is-re
---

Clear denominators and write

```text
p_e=sum_(j=1)^m n_j w_j,        n_j in Z.               (1)
```

Uniformly enumerate consequences of the relator stream `R_e`, hence proofs
that two support words `w_i,w_j` represent the same element of `Gamma_e`.
In parallel enumerate partitions `P` of `{1,...,m}` for which

```text
sum_(j in B) n_j=0             for every block B in P.   (2)
```

Accept when the equality enumerator has proved all words in every block of
one such `P` equal.  Acceptance is sound by `(2)`.  Conversely, if `p_e=0`,
partition its finite support by actual equality in `Gamma_e`.  Every equality
class has coefficient sum zero, and the finitely many within-class equality
proofs eventually appear.  Hence the procedure accepts exactly when
`p_e=0`.

Let

```text
Z={e:p_e=0 in Q[Gamma_e]}.
```

The preceding uniform search makes `Z` recursively enumerable.  By `(EGD2)`,
`NONHALT subseteq Z`; by `(EGD1)`, `HALT` is disjoint from `Z`.  Since every
index either halts or does not, `Z=NONHALT`.  Ordinary simulation enumerates
`HALT`, so dovetailing the two enumerators decides every input, contradicting
undecidability of the halting problem.

The cited finite-presentation word-problem enumerator is more than enough.
For a uniformly recursively enumerable presentation, the same proof simply
dovetails enumeration of the relator stream with enumeration of finite
normal-closure derivations; every valid equality proof uses only finitely
many relators.
