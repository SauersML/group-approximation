---
rg: 2
id: relative-automorphism-action-citation
kind: route
title: Import Belk-Fournier-Facio-Hyde-Zaremsky Propositions 2.3 and 2.6
target: relative-automorphism-action-is-highly-transitive
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Citation import.  Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2,
Propositions 2.3 and 2.6, read from source 2026-08-17; quotations in
`research/artifacts/boone-higman-audit-2026-08-17.md` §A.1.

Not reproved here and no Lean counterpart exists.

## What is deliberately excluded from the target

Faithfulness.  Their proof of it needs `S` to be mixed identity free, and
their own text says that is the only place the hypothesis is used.  The
target claim therefore states transitivity and stabilizers only, and the
route into `boone-higman-conjecture` gets faithfulness by passing to the
quotient by the action kernel instead — which is precisely why that route's
open input is a finite-presentation statement about the quotient.

The freeness of the translation action of `S` on `X`, which is what gives
`K ∩ S = 1` and keeps the core embedded in the quotient, is also taken from
the same source's analysis of the action.

## Trust surface

Only the two propositions are consumed, and only for `S` finitely generated,
infinite and simple.  The paper's headline results — Boone--Higman
embeddings for `Aut(F_n)` and for mapping class groups — are not used and
would not repair the route if the propositions failed.
