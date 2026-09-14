---
rg: 2
id: first-order-fundamental-group-closed-under-amplification
kind: claim
title: The first-order fundamental group is a closed subgroup of R_+ and elementary equivalence survives amplification
artifacts:
  - research/artifacts/hl-free-group-factors-2026-09-13.md
---

For a II_1 factor `M` let `F_fo(M) = { t in R_+ : M_t is elementarily equivalent
to M }`.

1. `F_fo(M)` is a closed subgroup of the multiplicative group `R_+`, containing
   the fundamental group `F(M)`.
2. If `M` and `N` are elementarily equivalent II_1 factors, then `M_t` and `N_t`
   are elementarily equivalent for every `t in R_+`.

Literature import, verbatim from the TeX of Goldbring–Pi, arXiv:2305.08168:

- l.388: "In \cite{GoldbringHart16}, the first-named author and Hart introduced the \textbf{first-order fundamental group} $\mathcal{F}_\fo(\mathcal{M}):=\{t \in \bR_+ \ : \ \mathcal{M}_t \equiv \cM\}$ of a II$_1$ factor $\cal M$. [...] It was shown there that $\cal F_{fo}(\cal M)$ is a closed subgroup of $\bb R_+$ containing the ordinary fundamental group $\cal F(\cal M)$ as a subgroup."
- l.339 (a lemma proved there, l.336–351): "Let $\cM, \cal{N}$ be $II_1$ factors satisfying $\cM \equiv \cal{N}$. Then for any $t\in \bR_+$, we have $\cM_t \equiv \cal{N}_t$."

Trust surface: item 1 is second-hand (Goldbring–Hart, as quoted); item 2 is
stated and proved in Goldbring–Pi, statement-level use only.
