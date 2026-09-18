---
rg: 2
id: tucker-drob-sandwich-sets-open-at-free-actions-citation
kind: route
title: Import Tucker-Drob's Lemma 6.2, the sets A_{F,r}, Theorem 6.4 and Corollaries 6.19 and 6.20
target: tucker-drob-sandwich-sets-open-at-free-actions
requires: []
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
---

Citation import, not a reproof. Source: R. Tucker-Drob, *Shift-minimal groups,
fixed price 1, and the unique trace property*, arXiv:1211.6395. Read from the
TeX source (`4_15_2012_Shift-minimal_groups.tex`, subsection `sec:infgen`,
"Cost and weak containment in infinitely generated groups") on September 17,
2026. The standing convention of the paper, verbatim: "Throughout, $\Gamma$
denotes a countable discrete group."

- Lemma `lem:open`, verbatim: "Let $F\subseteq \Gamma$ be finite and let
  $r\in \R \cup \{ \infty \}$. Then the following are equivalent for a measure
  preserving action $\bm{a} =\Gamma \cc ^a (X,\mu )$ of $\Gamma$: (1) There
  exists a sub-equivalence relation $E$ of $E_a$ such that
  $E_{a\resto \langle F\rangle}\subseteq E\subseteq E_a$ and $C_\mu (E) < r$.
  (2) There exists a finite $Q\subseteq \Gamma$ containing $F$ and a
  sub-equivalence relation $E$ of $E_a$ such that
  $E_{a\resto \langle F\rangle}\subseteq E\subseteq E_{a\resto\langle
  Q\rangle}$ and $C_\mu (E) < r$." Item (3) of the lemma, a graphing-distance
  criterion, is not used.
- Definition, verbatim: "For each finite $F\subseteq \Gamma$ and
  $r\in \R\cup \{ \infty \}$ let $A_{F,r}= A_{F,r}(\Gamma ,X,\mu )$ denote the
  set of $\bm{a}\in A(\Gamma ,X,\mu )$ that satisfy any -- and therefore all --
  of the equivalent properties (1)-(3) of Lemma \ref{lem:open}."
- The sentence after it, verbatim: "It is clear that the set
  $A_{F,r}(\Gamma ,X,\mu )$ is an isomorphism-invariant (and in fact,
  orbit-equivalence-invariant) subset of $A(\Gamma ,X,\mu )$."
- Theorem `thm:KecOpen`, verbatim: "Let $\Gamma$ be an infinite countable
  group. For each finite $F\subseteq \Gamma$ and $r\in \R \cup\{ \infty \}$ the
  set $A_{F,r}(\Gamma ,X,\mu )\cap \mbox{\emph{FR}}(\Gamma ,X,\mu )$ is
  contained in the interior of $A_{F,r}(\Gamma ,X,\mu )$. In particular,
  $A_{F,r}(\Gamma ,X,\mu )\cap \mbox{\emph{FR}}(\Gamma ,X,\mu )$ is open in
  $\mbox{\emph{FR}}(\Gamma ,X,\mu )$."
- Corollary `cor:PCdef`, verbatim: "Let $\bm{a}=\Gamma \cc ^a (X,\mu )$ be a
  m.p.\ action of $\Gamma$. Then $PC(\bm{a})\leq r$ if and only if
  $\bm{a}\in A_{F,r+\epsilon}$ for every finite $F\subseteq \Gamma$ and
  $\epsilon >0$."
- Corollary `cor:AFrPC`, verbatim: "Let $\bm{a} = \Gamma \cc ^a (X,\mu )$ and
  $\bm{b} =\Gamma \cc ^b(Y,\nu )$ be measure preserving actions of a countable
  group $\Gamma$. Assume that $\bm{a}$ is free. If $\bm{a}\prec \bm{b}$ then
  $PC(\bm{b})\leq PC(\bm{a})$."

The numbering 6.2, 6.4, 6.19 and 6.20 follows the tool table of
`research/artifacts/fpbs/docs/fixed-price-countable-passage.md`. The TeX labels
are given above.
