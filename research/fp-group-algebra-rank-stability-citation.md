---
rg: 2
id: fp-group-algebra-rank-stability-citation
kind: route
title: Import Bauer--Blachar--Greenfeld's group--algebra rank-stability equivalence
target: fp-group-rank-stability-equals-group-algebra-rank-stability
requires: []
---

**Source.** T. Bauer, G. Blachar, B. Greenfeld, *Rank-Stability of Polynomial Equations*, arXiv:2401.04676v2
(IMRN 2025, as recorded on `atlas-rank-stability-literature-fence`). TeX source `main_arxiv2.tex`, fetched on MSI on
2026-09-13.

**Numbering.** The source uses `\newtheorem{theorem}{Theorem}[section]`, and definitions, lemmas and propositions share
that counter. So Section 6 reads Definition 6.1, Lemma 6.2 (`lem:inv-diff`), Theorem 6.3 (`thm:group-alg`). The Atlas
fence node calls the theorem 6.2. The label is what is pinned here.

**Verbatim, l.650--652** (`thm:group-alg`):

> Let $G$ be a finitely presented group, and let $F$ be a field. Then $G$ is rank-stable over $F$ if and only if its
> group algebra $F[G]$ is rank-stable.

**Verbatim, l.625--628** (the group definition; the `\GL[d](F)` is a typo in the source for `\GL[n](F)`):

> Let $G=\left<x_1,\dots,x_d\mid P_1,\dots,P_r\right>$ be a finitely presented group, and let $F$ be a field. We say
> that $G$ is \textbf{rank-stable over $F$} if for every $\eps>0$ there exists $\delta>0$ such that the following holds:
> for any $n\ge 1$ and $A_1,\dots,A_d\in\GL[d](F)$ such that $\rank (P_j(A_1,\dots,A_d)-\Id_n)<\delta$ for all
> $1\le j\le r$, there exist $n'\ge 1$ and $B_1,\dots,B_d\in\GL[n'](F)$ such that
> $\Rank(\widehat{A_i}-\widehat{B_i})<\eps n$ for all $1\le i\le d$, and $P_j(B_1,\dots,B_d)=\Id_{n'}$ for all
> $1\le j\le r$.

**Verbatim, l.134--143** (`def:rank-stab`, the algebra definition), abridged only in layout:

> Let $\Alg=F\left<x_1,\dots,x_d\right>/\left<P_1,\dots,P_r\right>$ be a finitely presented algebra. We say that $\Alg$
> is \textbf{rank-stable} if for every $\eps>0$ there exists $\delta>0$ such that for every $n\in\N$ and every $d$-tuple
> of $n\times n$ matrices $\vec{A}=(A_1,\dots,A_d)$ satisfying: $\rank P_i(A_1,\dots,A_d) < \delta$ for all
> $1\le i\le r$ there exists $n'\in\N$ and a solution $\vec{B}=(B_1,\dots,B_d)$ of $n'\times n'$ matrices of
> $P_1,\dots,P_r$ such that $\Rank(\widehat{A_i}-\widehat{B_i}) < \eps n$ for all $1\le i\le d$.

The proof (l.654--694) was read. It passes through the presentation of `F[G]` with inverse letters `y_j` and the
relators `Q_i - 1`, `x_j y_j - 1`, `y_j x_j - 1`.
