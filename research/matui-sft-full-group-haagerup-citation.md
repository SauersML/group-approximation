---
rg: 2
id: matui-sft-full-group-haagerup-citation
kind: route
title: Import Matui's zipper-action theorem for topological full groups of one-sided irreducible shifts of finite type
target: sft-topological-full-groups-have-the-haagerup-property
requires: []
artifacts:
  - research/artifacts/hl-bh-groupoid-embedding-2026-09-13.md
---

Source: H. Matui, *Topological full groups of one-sided shifts of finite type*,
arXiv:1210.5800 (J. reine angew. Math. 705 (2015)). The TeX e-print
`tfgossftarXiv.tex` was fetched on MSI into
`/scratch.global/sauer354/hl-bh-groupoid-embedding/src/matui/` on 2026-09-13.
Quotes are verbatim; line numbers refer to that file.

- **Setting** (Subsection "The Haagerup property", l.2054–2058): "As in Section
  6.1, we let $G$ be the \'etale groupoid arising from a one-sided irreducible
  shift of finite type $(X,\sigma)$."
- **Where the statement comes from** (l.2061–2066): "we would like to see that
  $[[G]]$ has the Haagerup property, i.e. it is a-T-menable in the sense of M.
  Gromov. Indeed, this is a corollary of B. Hughes's theorem
  \cite[Theorem 1.1]{H09GGD}, which states that any locally finitely determined
  group of local similarities on a compact ultrametric space has the Haagerup
  property."
- **Theorem** (l.2109–2112): "The action $\phi:[[G]]\curvearrowright\Omega$ is
  a zipper action. In particular, $[[G]]$ has the Haagerup property."

Matui gives a self-contained proof of the theorem (l.2113 onward) and also
records the route through Hughes's theorem. This route imports the stated
theorem and does not re-derive it. The two standard facts in the target claim
(the Haagerup property passes to subgroups; property (T) plus the Haagerup
property forces a countable group to be finite) are taken from the same book as
`thompson-v-has-haagerup-property`, not re-read here.
