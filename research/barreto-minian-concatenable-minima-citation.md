---
rg: 2
id: barreto-minian-concatenable-minima-citation
kind: route
title: Import Barreto--Minian Theorem 2.5 and Definitions 2.2 and 2.4 verbatim from the arXiv TeX source
target: barreto-minian-concatenable-minima-give-local-indicability
requires: []
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
---

**Source.** A. N. Barreto and E. G. Minian, *Local indicability of groups with homology
circle presentations*, arXiv:2308.07447v1 (2023). Read at source on 2026-09-14 from the
e-print TeX file `locind.tex` (`https://arxiv.org/e-print/2308.07447`).

**Verbatim, Definition 2.2** (`\label{defmulti}`): "Let $r$ be a relator of a presentation
$\pe$ and let $m$ be the minimum value of the sequence of total exponents of its initial
subwords. We define the \textit{multiset of minima} $m(r)$ as the multiset that contains the
letters of $r$ with exponent $-1$ that attain the value $m$ and the letters that appear with
exponent $1$ in $r$ that attain the value $m+1$."

**Verbatim, Definition 2.4** (`\label{defconcatenable}`): "Given multisets $A_1, \ldots, A_n$
we say that they are \textit{concatenable} if there is an ordering $A_{i_1}, \ldots, A_{i_n}$
such that, for every $1 \leq j \leq n$, there exists an element in $A_{i_j}$ with multiplicity
$1$ that does not belong to the union of $A_{i_1}, \ldots, A_{i_{j-1}}$."

**Verbatim, Theorem 2.5** (`\label{main}`): "Let $\mathcal{P} = \langle a_1, \ldots, a_{k+2}
\ | \ r_1, \ldots, r_k, s \rangle$ be a presentation (of deficiency $1$) of a group $G$ with
$H_1(G)=\Z$ (for some $k\geq 0$), where all the relators are cyclically reduced and have total
exponent $0$. If the multisets of minima $m(r_1), \ldots, m(r_k)$ are concatenable, then $G$ is
locally indicable."

**Verbatim, LOT relator minima** (Section 3): "Note that all relators have total exponent $0$
and, if $\Gamma$ is a LOT, $\pg$ has deficiency $1$ and it is a homology circle." and "given any
relator $r$ (corresponding to an edge $e$ of $\Gamma$), its $I$-sequence attains exactly two
minima, one at $\lambda(e)$ and the other one at $i(e)$, then $m(r)=\{\lambda(e), i(e)\}$."
Their LOT relator is $t(e)^{-1}\lambda(e)^{-1}i(e)\lambda(e)$, a cyclic permutation of
`i(e) λ(e) t(e)^-1 λ(e)^-1`.

**Verbatim, the open status** (Introduction): "Local indicability of LOT groups is an open
problem (that would imply asphericity of the associated presentations). In fact, it is not even
known whether all LOT groups are torsion-free."

The proof (Section 2 of the source) follows Howie's proof of his Theorem 6.2 through the
infinite cyclic cover, iterated rewrites of the omitted relator and Howie's reducibility
theorem; it was read but is not re-derived here.
