---
rg: 2
id: leavitt-path-algebras-are-steinberg-algebras-citation
kind: route
title: Clark–Sims, Equivalent groupoids have Morita equivalent Steinberg algebras, Example 3.2
target: leavitt-path-algebras-are-steinberg-algebras
requires: []
artifacts:
  - research/artifacts/un-blueprint-2026-09-13-part1.md
---

**Source.** L. O. Clark and A. Sims, *Equivalent groupoids have Morita equivalent Steinberg algebras*,
arXiv:1311.3701. Read from the arXiv TeX source on MSI, 2026-09-13
(`/scratch.global/sauer354/un/un-architect/1311.3701/main.tex`, lines 285–332).

**Verbatim (Example 3.2):** "Every Leavitt path algebra is a Steinberg algebra. To see this, let $E$ be an
arbitrary directed graph, $G_E$ the groupoid of Example~\ref{ex:graphgroupoid} and $R$ a commutative unital
ring. We show that the Leavitt path algebra $L_R(E)$ is isomorphic to $A_R(G_E)$."

**Proof mechanism in the source.**
- The indicator functions `q_v = 1_(Z(v))`, `t_e = 1_(Z(e,s(e)))` and `t_(e^*) = 1_(Z(s(e),e))` form a
  Leavitt `E`-family, so the universal property gives `π : L_R(E) -> A_R(G_E)`.
- The graded uniqueness theorem (Tomforde, Theorem 4.8) makes `π` injective.
- Each `1_(Z((μ,ν) \ F)) = t_μ t_(ν^*) − sum_(α ∈ F) t_(μα) t_((να)^*)` lies in the range. Compact open sets
  are finite disjoint unions of such sets, so `π` is surjective.

**Numbering.**
- Counted from the source's shared counter (`\newtheorem{example}[theorem]{Example}`, numbered within
  sections). The example is the second environment of Section 3, after one lemma.
- Clark–Edie-Michell, arXiv:1403.4684, TeX line 244, cites it as "[morita, Example~3.2]".

**Specialisation to `L_k(1,2)`.** See the target node: the rose `R_2` and the Cuntz groupoid.
