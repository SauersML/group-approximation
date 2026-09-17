---
rg: 2
id: compressed-subgroups-of-free-groups-are-l2-independent-citation
kind: route
title: Import Jaikin-Zapirain's equivalence of compressed, inert and L2-independent subgroups of free groups
target: compressed-subgroups-of-free-groups-are-l2-independent
requires: []
artifacts:
  - research/artifacts/fpbs-locally-free-fixed-pseudocost-2026-09-17.md
---

Citation import, not a reproof. Source: A. Jaikin-Zapirain, *Free groups are
L2-subgroup rigid*, arXiv:2403.09515v2. Read from the TeX source
(`l2subgrouprigid25.tex`) on September 17, 2026.

- Definitions, verbatim: "A finitely generated subgroup $H$ of a free group $F$
  is called {\bf compressed} if for any finitely generated subgroup $L$ of $F$
  containing $H$, $\rk(H)\le \rk(L)$, and it is called {\bf inert} if for any
  finitely generated subgroup $L$ of $F$, $\rk(H\cap L)\le \rk(L)$." and "We
  also say that $H$ is {\bf $L^2$-independent} in $F$ if the canonical map
  $$\D(F)\otimes_{\Q[H]}I_{\Q[H]}\to \D(F)\otimes_{\Q[F]}I_{\Q[F]}$$ is
  injective."
- `D(G)`, verbatim: "the strong Atiyah conjecture over $\mathbb{Q}$ (which
  states that the division closure $\mathcal D(G)$ of $\mathbb{Q}[G]$ in
  $\mathcal U(G)$ is a division ring)"; "In this paper we make use of Linnell's
  solution of the Strong Atiyah Conjecture for free groups".
- Corollary `inertcompressed`, verbatim: "Let $F$ be a free group and $H$ a
  finitely generated subgroup. Then the following are equivalent: (1) $H$ is
  compressed in $F$; (2) $H$ is inert in $F$; (3) $H$ is $L^2$-independent in
  $F$."

The paper proves the corollary from its Theorem `pibar` (§ "Proof of
\cref{inertcompressed}"). The proof was not re-checked here.
