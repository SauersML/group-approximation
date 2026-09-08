---
rg: 2
id: finite-context-relator-energy-misses-nontrivial-words
kind: claim
title: Fixed polynomial relator contexts cannot dominate a nontrivial word
distinct_from:
  nontrivial-words-have-no-relation-energy-domination: that tests only the same vector with no right contexts; this allows any finite family of polynomial right contexts and additive slack below two.
  finite-ball-permutations-realize-word-orbits: that realizes relators and a word at the base vector; this simultaneously annihilates all chosen polynomial-context relator errors and rules out their quadratic certificates.
artifacts:
  - research/artifacts/finite-context-relator-energy.md
---

For $G=F(S)/\langle\!\langle R\rangle\!\rangle$ with finite $S$, and
$w_G\ne1$, fix finitely many $(r_j,b_j)\in R\times\mathbb C[F(S)]$.
There are finite permutation matrices $U$ and a unit vector $\xi$ with

$$ (r_j(U)-I)b_j(U)\xi=0\quad\text{for all }j,
\qquad \|(w(U)-I)\xi\|^2=2.$$

Consequently no universal positive-operator domination of $|w(U)-I|^2$
by a constant times these squared context errors, with additive
$\varepsilon I$ for $0\leq\varepsilon<2$, holds in all matrix dimensions.
The finite family is chosen before the dimension and tuple.

This is an obstruction to this certificate class, not to a scalar global
operator-norm estimate or to the property-(T)-free existence goal. The
artifact contains the full proof. No Lean coverage or novelty is claimed.
