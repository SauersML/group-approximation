---
rg: 2
id: golod-shafarevich-infinite-pro-p-citation
kind: route
title: Import the Golod--Shafarevich criterion from Ershov's survey
target: golod-shafarevich-presentations-have-infinite-pro-p-completion
requires: []
artifacts:
  - research/artifacts/local-restricted-burnside-2026-09-13.md
---

Literature import, not a derivation. Source: M. Ershov, *Golod--Shafarevich
groups: a survey*, arXiv:1206.0490, file `gssurvey_revised.tex`, fetched on MSI
2026-09-13. Quotes are verbatim from the TeX.

- **Degree function** (l.934--940): "Let $X=\{x_1,\ldots, x_d\}$ and
  $U=\{u_1,\ldots, u_d\}$ be finite sets of the same cardinality. Let
  $F=F_{\phat}(X)$ the free pro-$p$ group on $X$, and let
  $\iota: F\to \Fp\lla U\rra^{\times}$ be the Magnus embedding. Define the degree
  function $D: F\to \dbN\cup\{\infty\}$ by $$D(f)=\deg(\iota(f)-1),$$ where $\deg$
  is the usual degree of a power series in $u_1,\ldots, u_d$."
- **GS condition** (l.944--951): "(i) A (pro-$p$) presentation $(X, R)$ is said to
  satisfy the {\it Golod-Shafarevich (GS) condition} if there exists
  $\tau\in (0,1)$ such that $1-|X|\tau+H_R(\tau)<0$ where
  $H_R(t)=\sum_{r\in R}t^{D(r)}$. (ii) A pro-$p$ group $G$ is called a
  {\it Golod-Shafarevich (GS)} group if it has a presentation satisfying the GS
  condition. (iii) An abstract group $G$ is called a {\it Golod-Shafarevich}
  group (with respect to $p$) if its pro-$p$ completion $G_{\phat}$ is
  Golod-Shafarevich."
- **Abstract presentations suffice** (Remark, l.954--960): "It is more common to
  call an abstract group $G$ Golod-Shafarevich if it has an {\it abstract}
  presentation $(X, R)$ s.t. $1-|X|\tau+H_R(\tau)<0$ for some $\tau\in (0,1)$.
  This condition is certainly sufficient for $G$ to be Golod-Shafarevich in our
  sense since if an abstract group $G$ is given by a presentation $(X, R)$, then
  its pro-$p$ completion $G_{\phat}$ is given by the same presentation $(X, R)$,
  considered as a pro-$p$ presentation (see, e.g., \cite[Lemma~2.1]{Lu1})."
- **Theorem `GSinf`** (l.966--974): "Golod-Shafarevich groups are infinite." From
  its proof: "If $G$ is a Golod-Shafarevich pro-$p$ group, then by construction
  $\Fp[[G]]$ is a Golod-Shafarevich algebra, hence infinite. [...] If $G$ is a
  Golod-Shafarevich abstract group, its pro-$p$ completion is infinite, as we
  just argued, so $G$ itself must be infinite."

**Assembly.** An abstract presentation satisfying the condition makes `G` a
Golod--Shafarevich group in sense (iii) (the Remark), so `G_p̂` is a
Golod--Shafarevich pro-p group, and Theorem `GSinf` makes it infinite. The
degree function on the abstract free group is the restriction of `D` along
`F(X) -> F_p̂(X)`, and `ι(x_i) = 1 + u_i`.

**Not used.** Line 1024 of the survey states `D(f^{p^k})=D(f)^{p^k}`, which reads
as a typo for `p^k D(f)`. The consuming route proves the lower bound it needs
directly.
