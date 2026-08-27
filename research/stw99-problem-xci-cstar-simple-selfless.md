---
rg: 2
id: stw99-problem-xci-cstar-simple-selfless
kind: claim
title: The reduced C*-algebra of every C*-simple group is selfless (STW Problem XCI)
root: true
distinct_from:
  stw99-problem-xc-cstar-simple-strict-comparison: that asks for strict comparison; this asks for Robert's selflessness, which implies strict comparison (Robert, Theorem 3.1) and is the refinement STW record as Problem XCI.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem XCI of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026)** (Robert).  Is `C*_r(F₂)` selfless?  If `G` is a
countable discrete C\*-simple group, is `C*_r(G)` selfless?

Selflessness (Robert, *Selfless C\*-algebras*, arXiv 2023): `(A, τ)` is
selfless when the first-factor embedding `A → (A, τ)^{*∞}` into the reduced
free product of infinitely many copies factors through a `*`-homomorphism
`A^ω → (A, τ)^{*∞}` restricting to the diagonal.  Selfless algebras are simple,
have strict comparison, and are purely infinite or have a unique trace which
is the unique quasitrace (Robert, Theorem 5.2, Proposition 2.2, Theorem 3.1).

The first part is solved: `C*_r(F_n)` is selfless for `n ≥ 2`
(Amrutam--Gao--Kunnawalkam Elayavalli--Patchell, arXiv 2024).  The second part
is open; the same paper settles it for acylindrically hyperbolic groups with
rapid decay and no nontrivial finite normal subgroup
(`agkp-acylindrically-hyperbolic-rd-groups-selfless`).
