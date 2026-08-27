---
rg: 2
id: agkp-acylindrically-hyperbolic-rd-groups-selfless
kind: claim
title: Acylindrically hyperbolic groups with rapid decay and no finite normal subgroups have selfless reduced C*-algebras
distinct_from:
  stw99-problem-xci-cstar-simple-selfless: that asks for selflessness over all C*-simple groups; this is the established theorem covering the acylindrically hyperbolic rapid-decay subclass.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Theorem B of Amrutam--Gao--Kunnawalkam Elayavalli--Patchell, *Strict
comparison in reduced group C\*-algebras* (arXiv 2024).**  If `G` is
acylindrically hyperbolic, has no nontrivial finite normal subgroups, and has
the rapid decay property, then `C*_r(G)` is selfless in Robert's sense; hence
it is simple, has strict comparison, and its unique trace is its unique
quasitrace.

Mechanism (STW Addendum 25.1): such groups are *selfless groups* --- mixed
identity free with a subexponential length control on the witnessing
homomorphisms `G * ℤ → G` --- and rapid decay promotes the approximate
embeddings to a `*`-homomorphism `C*_r(G * ℤ) → C*_r(G)^ω`, whose value on the
generator of `ℤ` is the Haar unitary selflessness needs.  Free groups `F_n`,
`n ≥ 2`, are covered, settling STW Problem LXXXIX.

Relevance here: the manuscript's acylindrically hyperbolic machinery
(`GroupApproximation/Manuscript/NonMF/AcylindricallyHyperbolic.lean`) produces
C\*-simple groups by Dahmani--Guirardel--Osin; rapid decay is the hypothesis
those constructions do not control.
