---
rg: 2
id: qc-qa-graph-gap-from-liu-lcs
kind: route
title: Feed the Liu-based linear-system gap into the existing CFI graph construction
target: qc-isomorphic-not-qa-isomorphic-graph-pair-exists
requires:
  - binary-lcs-perfect-qc-strict-qa-gap-exists
  - lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

Choose the binary system Ax=b from the first prerequisite. Its algebra
has a trace but no R^U representation. The second prerequisite gives
G_(A,b) is qc-isomorphic but not qa-isomorphic to G_(A,0). This proves the
existing graph-pair target without any new graph encoding theorem.

The graph conversion retains its existing AMRSSV and BCEHPSW attribution;
the group-to-linear-system conversion is Paddock--Slofstra/Slofstra. Jihao
Liu supplies the internality input in the upstream nonhyperlinear Leavitt
seed, with the separately credited Khanh finite-presentation input.
