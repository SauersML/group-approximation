---
rg: 2
id: nlts-hamiltonians-from-good-qldpc-codes
kind: claim
title: Good qLDPC code Hamiltonians are NLTS - every state of energy below eps n needs circuit depth Omega(log n)
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
distinct_from:
  quantum-pcp-constant-gap-local-hamiltonian: that is QMA-hardness of estimating ground energy at a constant gap; this is a circuit lower bound for low-energy states of one explicit frustration-free commuting family, which the conjecture needs but which gives no hardness by itself.
---

**ESTABLISHED BY CITATION** (Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4,
Theorem 1; STOC 2023).

There are a constant `eps>0` and an explicit family of `O(1)`-local
frustration-free commuting Hamiltonians `H^(n)=sum_(i=1)^m h_i^(n)` on `n`
particles with `m=Theta(n)` terms such that every family of states `psi_n` with
`tr(H^(n) psi_n) < eps n` has circuit complexity at least `Omega(log n)`.

The family consists of the CSS stabilizer Hamiltonians `H_X+H_Z` of good
(constant-rate, linear-distance) qLDPC codes whose classical codes cluster
approximate codewords (their Property 1). Good qLDPC codes exist by
Panteleev--Kalachev (arXiv:2111.03654v2, TeX `th:qLDPC`) and Leverrier--Zemor
(arXiv:2202.13641v3).

**Bearing on the root.** A QMA-hard constant-gap family whose low-energy states
all had constant depth would give NP witnesses, so NLTS is a necessary feature of
hard families if QMA is not in NP (the source's own remark). NLTS does not suffice:
these Hamiltonians are frustration-free with zero ground energy, and the source
does not require quantum local testability. It asks whether the techniques extend
to non-commuting Hamiltonians.
