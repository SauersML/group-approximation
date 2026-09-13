---
rg: 2
id: algebra-rank-instability-criterion-citation
kind: route
title: Import Bauer--Blachar--Greenfeld's instability criterion for algebras
target: amenable-f-g-quotient-ideal-makes-algebra-rank-unstable
requires: []
---

**Source.** T. Bauer, G. Blachar, B. Greenfeld, *Rank-Stability of Polynomial Equations*, arXiv:2401.04676v2, TeX
source `main_arxiv2.tex` fetched on MSI on 2026-09-13, Section 8 "Instability". With the shared theorem counter this
is Definition 8.1 (amenable algebras) and Theorem 8.2 (`thm:unstable`).

**Verbatim, l.1355--1360** (the definition):

> Let $\Alg$ be a finitely generated algebra, and let $S$ be a finite set of generators. We say that $\Alg$ is
> \textbf{amenable} if for every $\eps>0$ there exists a finite-dimensional subspace $V\le \Alg$ such that
> $\dim_F \left(SV+V\right) < (1+\eps)\cdot \dim_F V.$

**Verbatim, l.1363--1371** (`thm:unstable`):

> Let $\Alg$ be a finitely presented algebra with a non-zero ideal $I\vartriangleleft \Alg$ such that:
> The ideal $I$ is finitely generated as a left ideal of $\Alg$; the algebra $\Alg/I$ is amenable; and $\Alg/I$ has no
> finite-dimensional representations. Then $\Alg$ is not rank-stable.

**Proof read** (l.1392--1487). The steps:
- take Følner subspaces `V_i` of `A/I` for the degree-`m` monomials `T`;
- the matrices act as the generators on the `S`-interior `U_i` and as zero on a complement;
- relator defects are at most `|T| dim E_i / n_i -> 0`;
- a nearby exact solution `B` has `Z = ∩ ker f_mu(B)` of dimension at least `(1 - 4 eps d) n_i / 4 >= 1`, where the
  `f_mu` generate `I` as a left ideal;
- `Z` is `B`-invariant because `I` is a two-sided ideal, so `A/I` acts on `Z`, a contradiction.

The source's Remark 8.3(2) records that the one-sided finite generation hypothesis cannot be dropped: `F<x,y>` with
`I = <xy - yx - 1>` meets the other hypotheses and is rank-stable.
