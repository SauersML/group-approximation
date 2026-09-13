---
rg: 2
id: lodha-moore-commutator-simple-abelianization-z3-citation
kind: route
title: Import the Burillo--Lodha--Reeves theorem for G_0, the abelianization lemma, the compact-support proposition and the centre proposition
target: lodha-moore-commutator-simple-abelianization-z3
requires: []
---

**Source.**  J. Burillo, Y. Lodha and L. Reeves, *Commutators in groups of
piecewise projective homeomorphisms*, Adv. Math. 332 (2018) 34--56,
arXiv:1509.04586.  TeX source `lm.tex`, fetched through MSI on 2026-09-13.
Quoted verbatim:

- **Main theorem for `G_0`** (`thm2` environment, l.132--138): "The group $G_0$ satisfies the following:
  (1) $G_0^{\prime}$ is simple. (2) Every proper quotient of $G_0$ is abelian.
  (3) All finite index subgroups of $G_0$ are normal in $G_0$."
- **Lemma** `lem:31` (l.341--349): "The map $\{x,x_\mathtt{1},y_\mathtt{10}\} \to \zz^3$
  given by $x\mapsto(1,0,0)$, $x_\mathtt1\mapsto(0,1,0)$,
  $y_{\mathtt{10}}\mapsto(0,0,1)$ extends to a surjective homomorphism
  $\pi:G_0\to\zz^3$, with kernel being the commutator subgroup $G_0'=[G_0,G_0]$."
- l.377: "the image $\{\pi(x), \pi(x_\mathtt{1}), \pi(y_\mathtt{10})\}$ is a basis
  for $\zz^3$ we conclude that $\pi$ induces an isomorphism from $G_0/G_0'$ to
  $\zz^3$."
- **Proposition** `prop:commutator` (l.385--387): "The commutator $G_0'$ contains
  exactly those elements in $G_0$ which have compact support, and which have a
  total exponent in the $y$-generators equal to zero."
- **Proposition** `centre` (l.505--507): "The center of $G_0$ is trivial."

**Identification of generators.**  Burillo--Lodha--Reeves use the generating set
`{x, x_1, y_10}` of Lodha--Moore; Lodha--Moore identify it with `{a, b, c}`
(arXiv:1308.4250, `vN_fp.tex` l.444--446 and l.489--490).

Items 1--4 of the claim are Theorem 2 (1), Theorem 2 (2) with the centre
proposition, Lemma 3.1 with l.377, and the compact-support proposition. ∎
