---
rg: 2
id: affine-ug-easy-on-certifiably-hypercontractive-graphs
kind: claim
title: Affine unique games are solvable in polynomial time on certifiably hypercontractive constraint graphs, including noisy hypercube, short code and Johnson (BBKSS 2021)
distinct_from:
  affine-ug-easy-on-globally-hypercontractive-graphs: that is the Bafna--Minzer extension to graphs with a succinct characterization of non-expanding sets and to small completeness; this is the certifiable small-set-expander case with completeness near 1.
  elementary-abelian-galois-games-round-with-linear-loss: that rounds symmetric quotient instances over F_p^N; this solves arbitrary affine instances on structured constraint graphs through SoS.
---

**ESTABLISHED, BY CITATION.** Bafna--Barak--Kothari--Schramm--Steurer,
*Playing Unique Games on Certified Small-Set Expanders*, arXiv:2006.09969v3.

A graph `G` is `(lambda, C)` hypercontractive if every `f` in the span
`V_lambda(G)` of the eigenvectors with eigenvalue `>= 1 - lambda` satisfies
`E f^4 <= C (E f^2)^2`. It is `(lambda, C, D)`-certifiably hypercontractive when
this has a degree-`D` SoS proof.

* **Theorem 1.1.** For every `C > 0`, `lambda in (0,1)` and `D`, there is a
  polynomial-time algorithm `A` with the following guarantee. If `G` is
  `(lambda, C, D)`-certifiably hypercontractive and `I` is an affine unique
  games instance with constraint graph `G` and `val(I) = 1 - eps`, for
  `eps <= lambda^2/100`, then `A(I)` outputs an assignment of value at least
  `eps lambda^4/(64 C)`.
* **Corollaries 1.3, 1.4 and Theorem 1.5.** The same holds with a constant
  `tau > 0` independent of the alphabet on the `alpha`-noisy hypercube, the
  noisy short-code graph and the `(n, l, alpha)` Johnson graph.

**Bearing.** The hard instances for `unique-games-conjecture` cannot have
certifiably hypercontractive constraint graphs. By KKMO, affine UG suffices for
UGC, but that reduction does not preserve the constraint graph, so this is a
restriction on *which graphs* a proof may use, not a refutation. The authors
note that it is open whether constant-degree SoS solves UG on the non-noisy
Boolean cube.

DERIVATION affine-ug-easy-on-certifiably-hypercontractive-graphs-citation
