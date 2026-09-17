---
rg: 2
id: tucker-drob-pseudocost-exhaustion-bounds-citation
kind: route
title: Import Tucker-Drob's pseudocost definition, Corollary 6.8 and Proposition 6.26(1)
target: tucker-drob-pseudocost-exhaustion-bounds
requires: []
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Citation import, not a reproof. Source: R. Tucker-Drob, *Shift-minimal groups,
fixed price 1, and the unique trace property*, arXiv:1211.6395. Read from the
TeX source (`4_15_2012_Shift-minimal_groups.tex`) on September 17, 2026.

- Definition `def:pseudo`, verbatim: "Let $E_0,E_1,E_2,\dots$, and $E$ be m.p.\
  countable Borel equivalence relations on $(X,\mu )$. The sequence
  $(E_n)_{n\in \N}$ is called an \emph{exhaustion of $E$}, denoted
  $(E_n)_{n\in \N}\nnearrow E$, if $E_0\subseteq E_1\subseteq \cdots$, and
  $E=\bigcup _n E_n$. The \emph{pseudocost} of $E$, denoted $PC_\mu (E)$, is
  defined by $PC_\mu (E) = \inf \{ \liminf _n C_\mu (E_n) \csuchthat
  (E_n)_{n\in \N}\nnearrow E \}$. If $\bm{a}= \Gamma \cc ^a (X,\mu )$ is a
  m.p.\ action of a countable group $\Gamma$ then define the pseudocost of
  $\bm{a}$ by $PC(\bm{a}):=PC_\mu (E_a)$."
- Corollary `cor:PC=C`, verbatim: "Let $E$ be a m.p.\ countable Borel
  equivalence relation on $(X,\mu )$. (1) If $C_\mu (E) <\infty$ then $PC_\mu
  (E)=C_\mu (E)$. (2) If $E$ is treeable then $PC_\mu (E)=C_\mu (E)$. (3)
  $PC_\mu (E)=1$ if and only if $C_\mu (E) =1$."
- Proposition `prop:analogue`(1), verbatim: "Let $\Gamma$ be a countably
  infinite group. (1) Suppose that $C(\Gamma )<\infty$. Then for any free
  m.p.\ action $\bm{b}=\Gamma \cc ^b (X,\mu )$ of $\Gamma$, and any exhaustion
  $(E_n)_{n\in \N}$ of $E_b$, we have $\liminf _{n\ra\infty} C_\mu (E_n) \geq
  C(\Gamma )$. Hence $PC(\Gamma )=C(\Gamma )$."

Numbering 6.6, 6.8 and 6.26 follows the passage artifact's tool table. The TeX
labels are given above.
