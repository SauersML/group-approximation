---
rg: 2
id: amenable-normalish-kills-l2-betti-bounded-cohomology-citation
kind: route
title: Import BKKO Propositions betti and trivial-bdd-cohomology
target: amenable-normalish-kills-l2-betti-bounded-cohomology
requires: []
artifacts:
  - research/artifacts/sk-cstar-simple-2-2026-09-13-part1.md
---

Citation import. The statements were read on 2026-09-13 from the arXiv e-print TeX source of Breuillard–Kalantar–Kennedy–Ozawa,
*C*-simplicity and the unique trace property for discrete groups*, arXiv:1410.2518
(`/scratch.global/sauer354/sk/sk-cstar-simple-2/1410_2518/main.tex`, Subsection `sec:cohomology`). Verbatim up to macros:

Proposition `betti` (l.626–628), introduced as "the following special case of \cite{BFS2013}*{Theorem 1.3}":
> Let $G$ be a discrete group. If $G$ contains an amenable normalish subgroup, then $\beta_n^{(2)} = 0$ for every $n \geq 0$.

Mixing modules (l.644–645):
> The dual Banach $G$-module $E$ is said to be {\em mixing} if the stabilizer subgroup $G_x = \{ s \in G \mid sx = x \}$ is
> finite for every $x \in E \setminus \{0\}$. Examples of such $G$-modules include $\ell^p(G)$ for $1\le p < \infty$.

Proposition `thm:trivial-bdd-cohomology` (l.647–649):
> Let $G$ be a discrete group, and let $(\pi,E)$ be a coefficient $G$-module with $E$ mixing. If $G$ contains an amenable
> normalish subgroup, then $H_b^n(G,E)$ is trivial for every $n \geq 0$ and every mixing dual Banach $G$-module.

**Proof of the second proposition** (l.651–657), re-derived. Compute `H_b^*(G,E)` through the complex `ℓ^∞((G/H)^{*+1},E)^G`.
- Each value `f(t_0H,…,t_nH)` is invariant under `⋂_i t_iHt_i^{-1}`.
- That intersection is infinite, and nonzero vectors of a mixing module have finite stabilizers. So `f = 0`.

**Scope.**
- Bader–Furman–Sauer Theorem 1.3 itself was not opened.
- Journal data are recalled: BKKO, Publ. Math. IHÉS 126 (2017); Bader–Furman–Sauer, *Weak notions of normality and vanishing
  up to rank in L²-cohomology*, IMRN (2014).
