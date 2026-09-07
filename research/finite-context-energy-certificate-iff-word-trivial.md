---
rg: 2
id: finite-context-energy-certificate-iff-word-trivial
kind: claim
title: Finite-context quadratic relator certificates characterize trivial words
distinct_from:
  finite-context-relator-energy-misses-nontrivial-words: that is the countermodel direction; this adds the converse and an explicit integral sum-of-squares certificate from any normal-closure expression.
  nontrivial-words-have-no-relation-energy-domination: that rules out one context-free inequality for nontrivial words; this characterizes exactly which words admit arbitrary finite-context inequalities.
artifacts:
  - research/artifacts/finite-context-relator-energy.md
---

For a finite generating presentation $G=F(S)/\langle\!\langle R\rangle\!\rangle$,
$w=1$ in $G$ if and only if there exist finitely many $r_j\in R$,
$b_j\in\mathbb C[F(S)]$, and $C\geq0$ such that

$$ |w(U)-I|^2\leq C\sum_j b_j(U)^*|r_j(U)-I|^2b_j(U) $$

for every finite-dimensional unitary tuple $U$. Allowing additive slack
$\varepsilon I$ with $0\leq\varepsilon<2$ gives the same class of words.

An expression of $w$ as $N$ conjugates of relators or inverse relators
supplies word contexts, $C=N$, and an exact free group ring identity with
$N(N-1)/2$ squares (with the empty case handled separately). This is an
upper bound from a supplied expression, not a certificate-minimality claim.
