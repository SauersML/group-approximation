---
rg: 2
id: li-shen-amalgamated-rfd-criterion-citation
kind: route
title: Import Li–Shen Theorem 2 and Example 1, read at source in the journal PDF
target: li-shen-amalgamated-rfd-criterion
requires: []
artifacts:
  - research/artifacts/sk-rfd-amalgam-2026-09-14-part1.md
---

Read 2026-09-14 from the journal PDF on Project Euclid (Illinois J. Math. 56 (2012), no. 2, pp. 647–659), pages 650 and 657.

**Theorem 2 (p. 657), verbatim.**
> Let $\mathcal A$, $\mathcal B$ be separable unital C*-algebras and $\mathcal D$ be a finite-dimensional C*-algebra. Suppose $\psi_{\mathcal A}\colon\mathcal D\to\mathcal A$ and $\psi_{\mathcal B}\colon\mathcal D\to\mathcal B$ are unital embeddings. Then $\mathcal A *_{\mathcal D}\mathcal B$ is RFD if and only if there are unital embeddings $q_1\colon\mathcal A\to\prod_{n=1}^\infty\mathcal M_{k_n}(\mathbb C)$ and $q_2\colon\mathcal B\to\prod_{n=1}^\infty\mathcal M_{k_n}(\mathbb C)$ for a sequence $\{k_n\}_{n=1}^\infty$ of integers such that the following diagram commutes

The diagram is the square $\mathcal D\hookrightarrow\mathcal A\to\prod\mathcal M_{k_n}$, $\mathcal D\hookrightarrow\mathcal B\to\prod\mathcal M_{k_n}$, that is, $q_1\circ\psi_{\mathcal A}=q_2\circ\psi_{\mathcal B}$.

**Proof in the source.**
- Necessity: restrict a unital embedding of $\mathcal A *_{\mathcal D}\mathcal B$ into $\prod\mathcal M_{k_n}$.
- Sufficiency: reduce to an abelian amalgam $P\mathcal D P$ through Brown–Dykema Lemma 2.2, then Proposition 2 (abelian finite-dimensional amalgam inside $\prod\mathcal M_{k_n}$ gives RFD), proved with Lemmas 2–5 (unitary perturbation of families of projections, Voiculescu-type approximate equivalence via Davidson Theorem II.5.8, compatible finite-dimensional subrepresentations).

**Example 1 (p. 650), verbatim in substance.** With $\varphi_1(1\oplus0)=\mathrm{diag}(1,0)$ in $M_2(\mathbb C)$ and $\varphi_2(1\oplus0)=\mathrm{diag}(1,0,0)$ in $M_3(\mathbb C)$, the algebra $M_2(\mathbb C) *_{\mathbb C\oplus\mathbb C} M_3(\mathbb C)$ is not MF: a tracial state would give $1/2=1/3$.

**Remark 2 (p. 650).** For finite-dimensional $\mathcal A$ and $\mathcal B$, Armstrong–Dykema–Exel–Li (Proc. Amer. Math. Soc. 132 (2004), 2019–2030) show that $\mathcal A *_{\mathcal D}\mathcal B$ is RFD iff there are faithful tracial states on $\mathcal A$ and $\mathcal B$ whose restrictions to $\mathcal D$ agree.
