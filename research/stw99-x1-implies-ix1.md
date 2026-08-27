---
rg: 2
id: stw99-x1-implies-ix1
kind: route
title: Amenable-implies-quasidiagonal for traces gives quasidiagonality of nuclear algebras with a faithful trace
target: stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal
requires: [stw99-problem-x1-amenable-traces-quasidiagonal]
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

Let `A` be separable nuclear with faithful trace `τ`.  Nuclearity makes every
trace amenable (Connes--Haagerup--Kirchberg; the repository's typed input
`NuclearAmenableTraceInput`, produced from the completely positive
approximation property in `Analysis.LanceNuclearAmenable`).  Under the premise
`τ` is quasidiagonal.  A faithful quasidiagonal trace gives an isometric
`*`-homomorphism into the norm corona `∏M_k/⊕M_k`, so `A` is MF
(`QuasidiagonalTraceModel.toMFTraceModel` and the MF-trace recognition
theorems), and a nuclear MF algebra is NF, i.e. quasidiagonal
(Blackadar--Kirchberg, Math. Ann. 307 (1997), Theorem 5.2.2; Lean
`blackadarKirchberg_isNFAlgebra_of_isNuclear_of_isMFAlgebra`).

STW state the implication in the paragraph before Problem X.  A Lean module
formalizing this route over the repository's existing predicates is being
authored under `GroupApproximation/Manuscript/NinetyNineProblems/`.
