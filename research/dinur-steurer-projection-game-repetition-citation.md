---
rg: 2
id: dinur-steurer-projection-game-repetition-citation
kind: route
title: Import Theorem [Product of different games] of Dinur--Steurer, Analytical Approach to Parallel Repetition (STOC 2014)
target: dinur-steurer-projection-game-repetition-bound
requires: []
---

Literature import, credited in full.

Irit Dinur, David Steurer, *Analytical Approach to Parallel Repetition*,
Proceedings of the 46th ACM Symposium on Theory of Computing (STOC 2014),
arXiv:1305.1979. Verified on 2026-09-17 from the arXiv v1 LaTeX source
(`productgames-arxiv1.tex`), Section 1.

* Model: "A one-round two-player game $G$ consists of a bipartite graph with
  vertex sets $U,V$ and edge set $E$, and a constraint
  $\pi_{uv}\subseteq \Sigma\times\Sigma$ per edge $uv\in E$." Its footnote:
  "Later, we will also allow non-negative weights on the edges. The
  definitions and results extend in the expected way."
* Value: "$\val(G) = \max_{f,g}\Prob[uv\in E]{\vbig \bigparen{f(u),g(v)}\in \pi_{uv}}$."
* Repetition: "In the $k$-fold parallel repetition $G^{\ok}$, the referee
  selects $k$ edges $u_1v_1,\ldots,u_kv_k\in E$ independently at random and
  sends a question tuple $u_1,\ldots,u_k$ to Alice, and $v_1,\ldots,v_k$ to
  Bob. Each player responds with a $k$-tuple of answers and they succeed if
  their answers satisfy each of the $k$ constraints."
* Projection games (footnote): "In a projection game, for any two questions
  $u$ and $v$ to the players and any answer $\beta$ of $Bob$, there exists at
  most one acceptable answer $\alpha$ for Alice."
* **Theorem [Product of different games].** "Let $G_1,\ldots,G_k$ be
  projection games. Then
  $\val(G_1\otimes \cdots \otimes G_k)^2 \le \prod_{i=1}^k \frac{2\sqrt{\delta_i}}{1+\delta_i}$
  where $\delta_i = \val(G_i)$."

A unique game, where each `pi_uv` is the graph of a permutation, is a
projection game: given Bob's answer, exactly one answer of Alice is accepted.
Taking `G_i = G` gives the stated bound for `G^(x t)`. The product game of a
unique game is the unique game described in the claim, because a tuple of
permutation constraints is a permutation of `[k]^t`.

The exponential form follows from the monotonicity and the series expansion
written out in the claim. `square`
