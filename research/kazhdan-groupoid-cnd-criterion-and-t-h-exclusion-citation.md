---
rg: 2
id: kazhdan-groupoid-cnd-criterion-and-t-h-exclusion-citation
kind: route
title: Import Anantharaman-Delaroche's cnd criterion for groupoid property (T) and the (T)/(H) exclusion
target: kazhdan-groupoid-cnd-criterion-and-t-h-exclusion
requires: []
artifacts:
  - research/artifacts/kazhdan-relation-coamenability-collapse-2026-09-17.md
---

Citation import. Read on 2026-09-17:
- AD05, arXiv:math/0308158v1, from arxiv.org/html, converted to text;
- AD11, arXiv:1105.5961, from ar5iv, converted to text.

The verbatim quotes are in Section 1 of the artifact:
- AD05: Definition 3.2, Lemma 4.1, Definitions 4.2 and 4.3, Definition 5.19, Theorem 5.18 and Theorem 5.22;
- AD11: the definition of an inessential reduction, Theorem 6.5, Theorem 8.4 (Ueda), Theorem 9.2, Corollary 9.4 with
  its one-line proof, and the Section 10.4 remark.

Two key quotes:
- "Theorem 5.22. Let $(G,C)$ be an ergodic $r$-discrete measured groupoid. The following conditions are equivalent:
  (i) $(G,C)$ has property $T$. (ii) For every real conditionally negative definite function $\psi$, there exists a
  Borel subset $E\subset G^{(0)}$ of positive measure, such that the restriction of $\psi$ to $G|_{E}$ is bounded."
- "Theorem 9.2. Let $(G,\mu)$ be an ergodic countable measured groupoid. We assume that $(G^{(0)},\mu)$ is a diffuse
  standard probability space. Then $(G,\mu)$ cannot have simultaneously properties (T) and (H)."

Hypothesis match: every use in `kazhdan-relations-coamenable-subrelations-locally-kazhdan-proof` is on an ergodic
countable p.m.p. equivalence relation, which is r-discrete, on a diffuse standard space.
