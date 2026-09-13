---
rg: 2
id: every-braid-group-is-cat0-via-diagonal-links
kind: route
title: Braid groups are CAT(0) once all noncrossing partition diagonal links are CAT(1)
target: every-braid-group-is-cat0
requires:
  - noncrossing-partition-diagonal-links-are-cat1
---

Brady–McCammond, arXiv:0909.4778 (Algebr. Geom. Topol. 10 (2010)), as quoted by Haettel–Kielak–Schwer
(arXiv:1304.5990v2):

- HKS Theorem 2.34 = [BM, Theorem 5.10 and Lemma 5.8]: if for all `3 <= k <= n` the diagonal link of `|NCP_k|`
  contains no unshrinkable short loop, then `|NCP_n|` is CAT(0). A CAT(1) space has no unshrinkable short loop
  (Bowditch; HKS Theorem 2.32).
- HKS Proposition 2.35 = [BM, Proposition 8.3]: if `|NCP_m|` is CAT(0) for all `m <= n`, then `B_n` acts
  geometrically on a CAT(0) space. The geometric input is T. Brady's compact `K(B_n, 1)` from the dual Garside
  structure (Adv. Math. 161 (2001) 20–40), isometric to a quotient of `|NCP_n|` (Jeong §2.4).

So if every `X_n` is CAT(1), every `B_n` is CAT(0).
