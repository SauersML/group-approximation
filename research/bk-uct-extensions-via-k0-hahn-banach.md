---
rg: 2
id: bk-uct-extensions-via-k0-hahn-banach
kind: route
title: Hahn-Banach for every ideal gives the QD extension property, hence quasidiagonality from stable finiteness
target: blackadar-kirchberg-for-uct-quotient-extensions
requires: [brown-dadarlat-qd-extensions-and-k0-hahn-banach, every-separable-nuclear-qd-algebra-has-k0-hahn-banach]
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

Brown--Dadarlat Theorem 4.11 turns the universal K_0-Hahn--Banach property
into the K_0-embedding property, and then the QD extension property, for
every separable nuclear quasidiagonal ideal.

Moutzouris Remark 2.5: tensor the extension with `K`.  Stable finiteness and
the hypotheses on `B` pass to `E tensor K` and `B tensor K`, and the QD
extension property of `I` (applied to `I tensor K`) makes `E tensor K`, hence
`E`, quasidiagonal.  The converse direction (quasidiagonal implies stably
finite) is standard.
