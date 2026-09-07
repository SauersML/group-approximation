---
rg: 2
id: finite-ball-permutations-realize-word-orbits
kind: claim
title: Finite permutations realize prescribed word orbits on one vector
artifacts:
  - notes/PROPERTY_T_FREE_FINITE_BALL_LIMIT_2026-09-07.md
---

Let $G=\langle s_1,\ldots,s_m\mid R\rangle$, let $R_0\subseteq R$ be
finite, and let $w$ be a word nontrivial in $G$. There are permutation
matrices $U_1,\ldots,U_m$ and a unit vector $\xi$ with

$$r(U)\xi=\xi\ (r\in R_0),\qquad
\|(w(U)-I)\xi\|=\sqrt2.$$

There is no finite-presentability hypothesis. This is an assertion about
one vector, not about operator-norm approximate representations. The
artifact gives the finite-ball proof; no novelty or Lean coverage claim
is made.
