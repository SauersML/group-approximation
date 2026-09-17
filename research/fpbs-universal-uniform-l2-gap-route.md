---
rg: 2
id: fpbs-universal-uniform-l2-gap-route
kind: route
title: A uniform l2 gap on uniformly nonamenable marked groups gives Benjamini-Schramm
target: fpbs-benjamini-schramm-universal
requires: [fpbs-uniform-l2-gap-marked-groups, fpbs-l2-gap-class-closed-under-local-limits]
artifacts:
  - research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md
---

SUFFICIENT route: Proposition 4.2 of
`research/artifacts/fpbs-l2-baire-kernel-2026-09-17.md`.

1. Let `Gamma` be nonamenable, with a finite symmetric generating set `S`,
   `e not in S`. List `S = {s_1,...,s_k}`. The simple Cayley graph of this
   marked group is `Cay(Gamma,S)`.
2. By Kesten, `rho(Cay(Gamma,S)) < 1`. So the marked group lies in
   `X_{k,eta}` for some `eta > 0`.
3. `fpbs-uniform-l2-gap-marked-groups` gives `(M,delta)` with
   `||T_{p_c+delta}|| <= M`.
4. Corollary 3.2 of `fpbs-l2-gap-class-closed-under-local-limits`, applied to the
   constant sequence, gives `p_c < p_c + delta <= p_{2->2} <= p_u`.

The route is conditional. Its hypothesis is a strictly stronger conjecture than
the goal. It is recorded because the hypothesis splits into finitely many
independently falsifiable cylinder pieces per `(k,eta)`
(`fpbs-uniform-l2-gap-from-relator-cylinders`), and one of those pieces, the
high-girth patch, has a drafted proof (`fpbs-high-girth-uniform-l2-patch`,
OPEN pending repair of the dichotomy claim it requires).
