---
rg: 2
id: linnell-dimension-equals-skew-field-rank-citation
kind: route
title: Import Linnell's theorem and Lück's torsion-free dimension comparison from Lück's survey
target: linnell-dimension-equals-skew-field-rank
requires: []
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Citation import, not a reproof. Source: W. Lück, *L2-invariants from the
algebraic point of view*, arXiv:math/0310489. Read from the TeX source
(`ltwoalg.tex`) on September 17, 2026.

- `D(G)`, verbatim: "The ring $\cald(G)$ appearing in the fundamental square
  [...] is the rational closure of $\bbC G$ in $\calu(G)$."
- Linnell's class, verbatim: "Let $\calc$ be the smallest class of groups,
  which contains all free groups and is closed under directed unions and
  extensions with elementary amenable quotients."
- Linnell's Theorem, verbatim: "Let $G$ be a group in $\calc$. Suppose that
  there exists $d \in \bbZ$, $d \ge 1$ such that the order of every finite
  subgroup of $G$ divides $d$. Then the ring theoretic version of the Atiyah
  Conjecture [...] for $G$ and hence the Atiyah Conjecture [...] for
  $(G,d,\bbC)$ are true." (Linnell 1993.)
- Remark "The ring theoretic version of the Atiyah Conjecture in the
  torsion-free case", verbatim: "Let $G$ be a torsion-free group. Then the
  ring theoretic version of the Atiyah Conjecture reduces to the statement
  that $\cald(G)$ is a skewfield. In this case we can assign to every
  $\cald(G)$-module $N$ its dimension $\dim_{\cald(G)}(N) \in \bbZ \amalg
  \{\infty\}$ in the usual way and we get for every $\bbC G$-module $M$
  $\dim_{\caln(G)}(\caln(G) \otimes_{\bbC G} M) = \dim_{\calu(G)}(\calu(G)
  \otimes_{\bbC G} M) = \dim_{\cald(G)}(\cald(G) \otimes_{\bbC G} M)$."

For torsion-free `G` in `C`, take `d = 1` in Linnell's Theorem. The Remark
then gives both bullets of the claim. The final sentence of the claim holds
because the inverse in `U(G)` of a nonzero element of a skew subfield already
lies in that subfield.
