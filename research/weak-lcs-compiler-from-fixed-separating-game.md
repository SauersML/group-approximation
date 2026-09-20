---
rg: 2
id: weak-lcs-compiler-from-fixed-separating-game
kind: route
title: A fixed separating LCS satisfies the weak machine-indexed promises by a constant map
target: perfect-completeness-constant-soundness-lcs-compiler
requires:
  - binary-lcs-perfect-qc-strict-qa-gap-exists
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

Fix one finite LCS L with perfect commuting value and quantum value less
than one, and set L_M=L for every machine M. This is a total computable
constant map: its existence does not require an algorithm to find L.
Both target promises hold regardless of M, and hence on their respective
halting and nonhalting cases. This proves precisely the weak interface as
written, not a halting decision reduction.

In particular its halting-side perfect strategy is commuting, not quantum.
It does NOT prove LIN-MIPstar_(1,s)=RE or remove Taller--Vidick's quantum
completeness loss. The original goal-equivalence node already explains
this constant-map phenomenon; this route now instantiates it with the
Liu-based finite-presented negative seed via Paddock--Slofstra.
