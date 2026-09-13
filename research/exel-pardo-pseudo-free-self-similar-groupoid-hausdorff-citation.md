---
rg: 2
id: exel-pardo-pseudo-free-self-similar-groupoid-hausdorff-citation
kind: route
title: Citation — Exel–Pardo arXiv:1409.1107, Definition EssFree, Proposition EssFreePath, Theorems MainHausdorff and CharacMinimal
target: exel-pardo-pseudo-free-self-similar-groupoid-hausdorff
requires: []
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part2.md
---

R. Exel and E. Pardo, *Self-similar graphs, a unified treatment of Katsura and Nekrashevych C*-algebras*,
arXiv:1409.1107. Quoted from the arXiv TeX source `main.tex`, fetched to MSI on 2026-09-13 and read directly.

- Standing Hypothesis (l.700): "Throughout this work we shall let $G$ be a countable discrete group, $E$ be a finite
  graph with no sources, $\auto $ be an action of $G$ on $E$, and" [a one-cocycle].
- Definition EssFree (l.1342): "We will say that $(\Data )$ is pseudo free if, whenever $(g,\ed ) \in G\times E^1$, is
  such that $g\ed = \ed $, and $\varphi (g,\ed )=1$, then $g=1$."
- Proposition EssFreePath (l.1351): "Suppose that $(\Data )$ is pseudo free and that a finite path $\alpha $ of nonzero
  length is strongly fixed for some $g$ in $G$. Then $g=1$."
- Theorem MainHausdorff (l.3347): "Assuming that $(\Data )$ satisfies \ref{StandingHyp}, the following are equivalent:
  (a) for every $g$ in $G$, there are at most finitely many minimal strongly fixed paths for $g$, (b) $\GpdGE $ is
  Hausdorff."
- Theorem CharacMinimal (l.3557): "Given $(G,E,\varphi )$ satisfying \ref{StandingHyp}, one has that the following are
  equivalent: (i) the standard action of $\SGE $ on $E^\infty $ defined in \ref{ActionOfSGE} is irreducible, (ii)
  $\GpdGE $ is minimal, (iii) $E$ is weakly $G$-transitive."

Item 2 of the claim is EssFreePath. Item 1 is MainHausdorff. Item 3 is CharacMinimal. The consequence combines items 1
and 2: for `g != 1` there are no minimal strongly fixed paths, and for `g = 1` only the vertices.
