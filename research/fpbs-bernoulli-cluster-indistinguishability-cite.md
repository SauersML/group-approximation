---
rg: 2
id: fpbs-bernoulli-cluster-indistinguishability-cite
kind: route
title: Import Lyons-Schramm cluster indistinguishability in its diagonal form
target: fpbs-bernoulli-cluster-indistinguishability
requires: []
---

Citation import, not a reproof. R. Lyons, O. Schramm, *Indistinguishability
of percolation clusters*, arXiv:math/9811170, Ann. Probab. 27 (1999)
1809--1836. Read from the arXiv TeX source (e-print math/9811170, tarball of
1999-05-02) on 2026-09-17. Verbatim, with TeX macros kept:

* Definition (label `d.inds`): "Let $G$ be graph and $\Gamma$ a closed
  (vertex-) transitive subgroup of $\Aut(G)$. Let $(\P,\omega)$ be a
  $\Gamma$-invariant bond percolation process on $G$. We say that $\P$ has
  {\bf indistinguishable infinite clusters} if for every measurable
  $\ev A\subset 2^{\verts(G)}\times 2^{\edges(G)}$ that is invariant under the
  diagonal action of $\Gamma$, almost surely, for all infinite clusters $C$ of
  $\omega$, we have $(C,\omega)\in\ev A$, or for all infinite clusters $C$, we
  have $(C,\omega)\notin\ev A$."
* Theorem (label `t.cerg`, Cluster Indistinguishability), with the standing
  assumption macro "Let $G$ be a graph with a transitive unimodular closed
  automorphism group $\Gamma$": "Every $\Gamma$-invariant, insertion-tolerant,
  bond percolation process on $G$ has indistinguishable infinite clusters."

Bernoulli(`p`) with `0<p<1` is insertion tolerant. The left-multiplication
action of a finitely generated group on its Cayley graph is a discrete, hence
closed and unimodular, vertex-transitive group of automorphisms.
