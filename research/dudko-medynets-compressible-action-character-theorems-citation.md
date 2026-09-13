---
rg: 2
id: dudko-medynets-compressible-action-character-theorems-citation
kind: route
title: Import the Dudko--Medynets compressibility definition, both character theorems and the dyadic interval lemma from the arXiv source
target: dudko-medynets-compressible-action-character-theorems
requires: []
---

**Source.**  arXiv:1212.1230, TeX source (`HigmanThompsonGroups.tex`), fetched
through MSI on 2026-09-13.  Quoted verbatim by label, since the source numbers
environments automatically:

- `DefinitionCompressibleBase` (l.139--145): "We will say that the action of $G$
  on $X$ is \emph{compressible} if there exists a base of the topology
  $\mathfrak{U}$ on $X$ such that (i) for every $g\in G$ there exists
  $U\in\mathfrak{U}\,$ such that $\supp(g)\subset U$; (ii) for every
  $U_1,U_2\in \mathfrak{U}\,$ there exists $g\in G$ such that
  $g(U_1)\subset U_2$; (iii) for every $U_1,U_2,U_3\in\mathfrak{U}$ with
  $\overline{U}_1\cap \overline{U}_2=\varnothing$ there exists $g\in G$ such that
  $g(U_1)\cap U_3=\varnothing$ and $\supp(g)\cap U_2=\varnothing$. (iv) for any
  $U_1,U_2\in \mathfrak{U}$ there exists $U_3\in\mathfrak{U}$ such that
  $U_3\supset U_1\cup U_2$."  The standing hypotheses (l.137): $X$ is a regular
  Hausdorff topological space, assumed infinite, and
  $supp(g) = \overline{\{x\in X : g(x)\neq x\}}$.
- `TheoremNoCharactersSimpleGroups` (l.205--206): "Let $G$ be a simple countable
  group admitting a compressible action on a regular Hausdorff topological space
  $X$. Then $G$ has no proper characters."  Definition (l.131): no proper
  characters means every indecomposable character is the identity character or
  the regular character.
- `TheoremCharactersNonSimpleGroups` (l.212--221): "Let $G$ be a group and $R$ be
  an ICC subgroup of $G$ such that (i) $R$ has no proper characters; (ii) for
  every $g\in G\setminus\{e\}$, there exists a sequence of distinct elements
  $\{g_i\}_{i\geq 1}\subset C_R(g)$ such that $g_i^{-1} g_j\in R$ for any $i,j$.
  Then each finite type factor representation $\pi$ of $G$ is either regular or
  has the form $\pi(g)=\omega([g])$, where $\omega$ is a finite factor
  representation of $G/N(R)$ and $[g]\in G/N(R)$ is the coset of the element $g$."
  Here (l.210) $C_R(g)=\{hgh^{-1}:h\in R\}$ and $N(R)$ is the normal closure of
  $R$ in $G$.
- l.114--115: "The indecomposable characters on a group $G$ are in one-to-one
  correspondence with the finite type factor representations of $G$."
- l.317: "all finite factor representations of abelian groups are scalar
  representations, i.e. $\pi(g) = c_g\id$".
- l.302: "Consider the subgroup $F_{n,r}^0$ of $F_{n,r}$ consisting of all elements
  $f\in F_{n,r}$ with $supp(f)$ being a subset of $(0,r)$. Observe that (the
  commutator subgroup) $F_{n,r}' = (F_{n,r}^0)'$."
- `LemmaRUConditions` (l.306--307): "The base of topology
  $\mathfrak{U}\,=\{(a,b):[a,b]\subset (0,r),a,b\in\mathbb Z[\tfrac{1}{n}]\}$
  satisfies the conditions (i)-(iv) of Definition \ref{DefinitionCompressible}
  for the action of the group $R = (F_{n,r}^0)'$ on $(0,r)$. Thus, the action of
  $R$ is compressible."  Their proof (l.309--315) is complete.

Items 1--4 of the claim restate these. ∎
