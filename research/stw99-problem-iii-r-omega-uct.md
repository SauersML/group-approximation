---
rg: 2
id: stw99-problem-iii-r-omega-uct
kind: claim
title: KK into the tracial ultrapower of R is computed by Hom on K_0 for separable nuclear algebras (STW Problem III)
root: true
distinct_from:
  stw99-problem-ii-nuclear-uct: that is the full UCT problem; this is its single-target instance at B = R-omega, the exact form of the UCT input to the Tikuisis--White--Winter quasidiagonality theorem and to KK-classification of finite strongly self-absorbing algebras.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that asks for operator-norm matrix models of R; this is a K-theoretic computation for the tracial ultrapower and neither implies the other, though both are the non-UCT residues of the same classification machinery.
artifacts:
  - research/artifacts/stw99-uct-cluster-2026-08-30.md
---

**Problem III of Schafhauser--Tikuisis--White ("the R^ω-UCT problem"),
arXiv:2506.10902.**  For separable nuclear `A`, is
`KK(A, R^ω) → Hom(K_0(A), R)` an isomorphism?  (`K_1(R^ω) = 0`,
`K_0(R^ω) ≅ R` via the trace.)

Known: it holds when `A` is a finite strongly self-absorbing algebra —
`R^ω` is a quotient of the norm-ultrapower `D_ω`, hence separably
`D`-stable, and Dadarlat--Winter compute `KK(D, ·) ≅ K_0` on `D`-stable
targets; this drives Schafhauser's KK-classification of finite strongly
self-absorbing algebras (arXiv 2024, Theorem C).  It follows from the
full UCT (`stw99-uct-implies-r-omega-uct`).

## Attempts

* The known case suggests the general strategy: exhibit enough separable
  `D`-stable subalgebras of `R^ω` absorbing the relevant Cuntz pairs; the
  obstruction is that a general nuclear `A` carries no self-absorption to
  transport.  STW record no counterexample candidate; a negative answer
  would produce a nuclear `A` and a Cuntz pair over `R^ω` invisible to
  `K_0`, i.e. a genuinely non-UCT phenomenon inside the hyperfinite
  ultrapower, and would block UCT-free classification along present
  lines.
* Relation to this session's X(2) lane: both problems ask whether the
  tracial ultrapower world is as rigid as the UCT/classification
  machinery predicts; the session's obstruction census for X(2) (no
  known non-quasidiagonal subalgebra of `R`) is weak evidence in the
  same rigidity direction.
