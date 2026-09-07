---
rg: 2
id: finite-context-energy-word-kernel-proof
kind: route
title: Telescope a normal-closure expression and expand pairwise squares
target: finite-context-energy-certificate-iff-word-trivial
requires:
  - finite-context-relator-energy-misses-nontrivial-words
artifacts:
  - research/artifacts/finite-context-relator-energy.md
---

The prerequisite rules out a certificate for a nontrivial word, including
slack below two. For a trivial word choose
$w=\prod_{j=1}^N a_j$ with $a_j=g_jr_j^{\epsilon_j}g_j^{-1}$.
Set $z_j=(a_1\cdots a_{j-1})(a_j-1)$, so $\sum_jz_j=w-1$.
For either sign of $\epsilon_j$, $z_j$ is a signed unitary left multiple
of $(r_j-1)g_j^{-1}$. The exact identity

$$N\sum_j z_j^*z_j-|\sum_jz_j|^2
=\sum_{i<j}|z_i-z_j|^2$$

gives the required certificate. Theorem 3 in the artifact supplies every
step, including inverse relators and the empty expression. This proof
uses no MF or property-(T) assertion.
