---
rg: 2
id: matui-kunneth-full-shift-homology-citation
kind: route
title: Import of Matui 2016, Theorem Kunneth, and Matui 2015 on homology of shift of finite type groupoids
target: matui-groupoid-homology-kunneth-and-full-shift-vanishing
requires: []
artifacts:
  - research/artifacts/hl-bh-a2-boundary-hosts-2026-09-14.md
---

**Sources.** H. Matui, *Étale groupoids arising from products of shifts of finite type*,
Adv. Math. 303 (2016), arXiv:1512.01724; H. Matui, *Topological full groups of one-sided
shifts of finite type*, J. reine angew. Math. 705 (2015), arXiv:1210.5800.

**How they were read.** Both arXiv e-print TeX sources were fetched on MSI on 2026-09-14
into `/scratch.global/sauer354/hl-bh-a2-boundary-hosts/src/`. Quotes are from those files.

**Verbatim.**
- arXiv:1512.01724, Theorem `Kunneth` (TeX l.451–459): "Let $\G$ and $\H$ be \'etale
  groupoids. For any $n\geq0$, there exists a natural short exact sequence
  $0\longrightarrow\bigoplus_{i+j=n}H_i(\G)\otimes H_j(\H) \longrightarrow H_n(\G\times\H)
  \longrightarrow\bigoplus_{i+j=n-1}\Tor(H_i(\G),H_j(\H))\longrightarrow0.$ Furthermore
  these sequences split (but not canonically)."
- arXiv:1210.5800, TeX l.212–220: "From $(X,\sigma)$, we can construct the \'etale groupoid
  $G$ by $G=\{(x,n,y)\in X\times\Z\times X\mid \exists k,l\in\N,\ n=k{-}l,\
  \sigma^k(x)=\sigma^l(y)\}$. By \cite[Theorem 4.14]{M12PLMS}, the homology groups $H_n(G)$
  of $G$ are $H_n(G)=\Coker(\id-M^t)$ for $n=0$, $\Ker(\id-M^t)$ for $n=1$, $0$ for
  $n\geq2$, where $M$ is the $k\times k$ matrix with entries in $\Z_+$ representing
  $(X,\sigma)$ and [...]"
