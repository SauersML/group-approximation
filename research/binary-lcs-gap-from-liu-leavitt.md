---
rg: 2
id: binary-lcs-gap-from-liu-leavitt
kind: route
title: Apply Paddock-Slofstra to the Liu-based finitely presented Leavitt witness
target: binary-lcs-perfect-qc-strict-qa-gap-exists
requires:
  - binary-leavitt-unit-group-is-not-hyperlinear
  - leavitt-unit-group-finitely-presented
  - lcs-tracial-ru-gap-equiv-nonhyperlinear
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

The first two prerequisites concern the same group L_(F_2)(1,2)^x.
Paddock--Slofstra Proposition 5.8 therefore supplies a finite binary linear
system with a tracial state and no R^U representation. Their Theorem 3.11
identifies these with a perfect commuting strategy and the absence of a
perfect strategy in C_qa. For a fixed full-support distribution, C_qa is
compact and the winning functional is continuous. Its maximum is less than
one, giving a positive gap uniformly over all finite-dimensional strategies.

Primary source: Connor Paddock and William Slofstra,
[Satisfiability problems and algebras of boolean constraint system games](https://arxiv.org/html/2310.07901v2),
Proposition 5.8 and Theorem 3.11(3)-(4). These literature implications are
being applied, not claimed as new reductions. The source negative group uses
Jihao Liu's [internality theorem](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf);
finite presentation uses Khanh's separately recorded theorem. No perfect
completeness strengthening of Taller--Vidick is assumed.
