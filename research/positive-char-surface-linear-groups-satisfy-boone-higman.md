---
rg: 2
id: positive-char-surface-linear-groups-satisfy-boone-higman
kind: claim
title: Finitely generated linear groups over positive-characteristic fields of transcendence degree at most two satisfy Boone--Higman
distinct_from:
  char-two-surface-linear-groups-satisfy-boone-higman: that is characteristic two; this is every positive characteristic, with hosts L_p ⊗ L_p modulo their scalar centres.
  char-two-curve-linear-groups-satisfy-boone-higman: that is characteristic two and transcendence degree at most one inside L^x; this is every prime and transcendence degree at most two.
artifacts:
  - research/artifacts/boone-higman-prime-field-leavitt-hosts-2026-09-12.md
---

**ESTABLISHED (conditional on the imports behind
`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`).** Let `K` be a field of
characteristic `p > 0` with transcendence degree at most two over `F_p`. Every
finitely generated subgroup of `GL_n(K)` embeds in the finitely presented simple
group `(L_p ⊗ L_p)^x / F_p^x`, and so satisfies Boone--Higman.

**Examples.**
- `SL_n(F_p[t_1, t_2])` for `n >= 3`.
- The finitely generated subgroups of `GL_n(F_q(t_1, t_2))`.
- `Z/p wr Z^2`.
- Baumslag's finitely presented metabelian group
  `<a, s, t | a^p, [s,t], [a, a^t], a^s = a a^t> = F_p[x^±, (1+x)^-1] ⋊ Z^2`,
  which contains `Z/p wr Z`. It is a positive-characteristic instance of the
  finitely presented metabelian case, Problem 5.3(7) of Belk--Bleak--Matucci--Zaremsky.

The Belk--Bleak--Matucci--Zaremsky survey arXiv:2306.16356v3 names no
positive-characteristic linear class. In characteristic zero only `GL_n(Q)` is
known (Zaremsky arXiv:2405.09722). The novelty search was bounded (2026-09-12).

DERIVATION
positive-characteristic-surface-linear-proof
