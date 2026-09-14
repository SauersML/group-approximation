---
rg: 2
id: surface-group-factors-are-free-group-factors
kind: claim
title: Group von Neumann algebras of closed surface groups of genus g are free group factors on 2g-1 generators
artifacts:
  - research/artifacts/hl-free-group-factors-2026-09-13.md
---

If `Lambda = pi_1(Sigma_g)` with `g >= 2`, then `L(Lambda) = L(F_{2g-1})`. More
generally, for a finitely generated torsion-free non-elementary discrete
subgroup of `PSL_2(R)`, the group factor is an interpolated free group factor.

Literature import, verbatim from the TeX of D. Shlyakhtenko, *On the II_1 factors
of Fuchsian groups* (arXiv:2609.11074, September 2026), fetched on MSI:

- Corollary `cor:torsionFreeAreFree` (l.155–161): "If $\Lambda$ is a torsion-free finitely degenerated non-elementary discrete subgroup of $PSL_{2}(\mathbb{R})$, then $L(\Gamma)\cong L(\mathbb{F}_{r})$ (where $r$ is as above). In particular, if $\Lambda=\pi_{1}(\Sigma_{g})$ is the fundamental group of a surface of genus $g\geq2$, then $L(\Lambda)\cong L(\mathbb{F}_{2g-1}).$"
- Abstract: "settling a conjecture of de la Harpe and Voiculescu".

Trust surface: a recent preprint, not refereed; the proof (free complementation
of `aba^{-1}b^{-1}` in `L(F_2)`) was not checked here. The typos
("degenerated", `Gamma` for `Lambda`) are in the source.

Consequence for `free-group-factor-isomorphism-problem`: none directly. Group
factors of non-free groups realize free group factors, so a candidate invariant
separating `L(F_m)` from `L(F_n)` must take the same value on
`L(pi_1(Sigma_g))` and `L(F_{2g-1})`.
