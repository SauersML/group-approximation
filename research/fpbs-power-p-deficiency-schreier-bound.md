---
rg: 2
id: fpbs-power-p-deficiency-schreier-bound
kind: claim
title: Power p-deficiency bounds the p-gradient from below
artifacts:
  - research/artifacts/fpbs/docs/power-p-deficiency-excludes-t-2026-09-11.md
---

For a finitely generated group `G` and a prime `p`, let `def_p(G)` be the
supremum over presentations `(X,R)` with `X` finite of
`|X| - 1 - sum_(r in R) p^(-nu_p(r))`. Here `nu_p(r)` is the largest `k` with
`r` a `p^k`-th power in the free group.

Then `d_p(G) >= def_p(G) + 1`. For every subnormal subgroup `H` of `p`-power
index, `def_p(H) >= def_p(G)[G:H]`, so

    (d_p(H) - 1)/[G:H] >= def_p(G),

where `d_p(H) = dim_(F_p) H_1(H;F_p)`. So positive power `p`-deficiency gives
positive `p`-gradient.

This is a literature import: Schlage-Puchta (arXiv:1105.1631, Theorem 2), as
stated in Ershov's survey Theorem 9.1. Relators may be infinite in number and
the group may be torsion.
