---
rg: 2
id: stw99-problem-x1-amenable-traces-quasidiagonal
kind: claim
title: Every amenable trace on a C*-algebra is quasidiagonal (STW Problem X(1))
root: true
refuted_by: [stw99-problem-x1-fails-on-full-group-algebras]
distinct_from:
  amenable-implies-operator-mf: that is the Rosenberg-conjecture theorem for amenable groups, the case of this question with a nuclear UCT algebra and a faithful trace; this asks the same question for every amenable trace on every C*-algebra, exact or not, faithful or not.
  mf-implies-hyperlinear: that compares two approximation properties of a group; this compares two approximation properties of a single trace on an arbitrary C*-algebra.
  stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal: that asks only about faithful traces on separable nuclear algebras and concludes quasidiagonality of the algebra; this asks about every amenable trace and concludes quasidiagonality of the trace, and it is the stronger question (route stw99-x1-implies-ix1).
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean
  - GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
  - research/artifacts/stw10-factorial-witness-audit-2026-08-30.md
---

**Problem X(1) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).**  Are amenable traces on C\*-algebras necessarily
quasidiagonal?

Definitions are Brown's (N. P. Brown, *Invariant means and finite representation theory of C\*-algebras*, Mem. Amer. Math. Soc. 184 (2006), no. 865).  A tracial state `τ` on a unital
C\*-algebra `A` is *amenable* (Kirchberg: *liftable*) when there are u.c.p.
maps `φₙ : A → M_{kₙ}` with `‖φₙ(ab) − φₙ(a)φₙ(b)‖₂ → 0` in the normalized
Hilbert--Schmidt norm and `tr ∘ φₙ → τ` pointwise (Brown, Theorem 3.1.6);
it is *quasidiagonal* when the same can be done with `‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0`
in operator norm (Brown, Definition 3.3.1).  Quasidiagonal traces are
amenable; the question is the converse.

The repository already carries both notions in Lean:
`Quasidiagonal.IsAmenableTrace` and `Quasidiagonal.IsQuasidiagonalTrace`
(`GroupApproximation/Analysis/TikuisisWhiteWinterCore.lean`,
`GroupApproximation/Analysis/QuasidiagonalTrace.lean`), with the easy
direction `isAmenableTrace_of_isQuasidiagonalTrace` proved.  So the question
is, verbatim,

```text
∀ (A : Type u) [CStarAlgebra A] (τ : TracialState A),
  IsAmenableTrace τ → IsQuasidiagonalTrace τ.
```

## What is known

* True for faithful traces on separable nuclear algebras satisfying the UCT
  (Tikuisis--White--Winter, Ann. of Math. 185 (2017); Gabe; Schafhauser).
  STW note that if Theorem 11 there (the AF-embedding form) held without the
  UCT, the question would be settled for all exact algebras, by the GNS
  reduction in their footnote 26.
* True for amenable traces on cones (Gabe; recorded as [53, Proposition 3.2]
  in STW).
* True for property (T) groups: Kirchberg's lemma converts Hilbert--Schmidt
  approximate representations of a Kazhdan group into honest finite-dimensional
  representations, so on `C*(Γ)` with `Γ` Kazhdan every amenable trace is
  quasidiagonal (Brown, Proposition 4.1.12).
* STW: the question "easily reduces to the case of separable C*-algebras", and
  for exact algebras to faithful traces; they expect the heart of the matter
  for non-exact algebras to be whether the trace of the hyperfinite II₁ factor
  is quasidiagonal (`stw99-problem-x2-hyperfinite-factor-quasidiagonal`).

## Why it is a root of this graph

For the full group C\*-algebra `C*(Γ)` with its canonical trace `τ_Γ`, the
two sides are group properties: `τ_Γ` is amenable exactly when `Γ` has
Kirchberg's factorization property (Brown, Theorem 4.1.9), and `τ_Γ` is
quasidiagonal exactly when `Γ` admits operator-norm asymptotic
finite-dimensional unitary representations recovering the regular character.
The repository's literal finitely presented group `E` is sofic and has a
central involution killed by every operator-norm corona representation, so its
canonical trace is a hyperlinear trace that is not quasidiagonal
(`literal-canonical-trace-hyperlinear-not-quasidiagonal`).  The one thing
standing between that fact and a negative answer to this problem is the
factorization property of `E` (`literal-group-factorization-property`).

Lean statement: `NinetyNineProblems.ProblemX1Statement` (`GroupApproximation/Manuscript/NinetyNineProblems/ProblemX.lean`).  The same
module proves `isHyperlinearTrace_of_isAmenableTrace` (an amenable trace is a
hyperlinear trace) and the conditional refutation
`not_problemX1Statement_of_literalFactorizationProperty`.

Positive instance machine-checked: on Kazhdan full group C\*-algebras the
answer is YES (`problemX1_restricted_to_kazhdan`, `GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean`, from Brown Prop
4.1.12 as a typed input); any group-algebra counterexample must be
non-Kazhdan, which the literal group `E` is designed to be.

## August 2026 audit and attempts

The universal question remains open.  Shulman's arXiv:2508.00125 adds a
homotopy-domination permanence theorem but does not resolve it.  The current
unconditional reductions are:

- `directed-unions-preserve-trace-approximations`, which makes both trace
  properties local on unital directed dense unions;
- `factorization-and-canonical-qd-are-finitely-local`, its full-group-algebra
  consequence;
- `exact-gns-kernel-amenability-reduction`, which isolates the exact faithful
  GNS-image reduction without asserting QD descent; and
- `nonamenable-factorization-regular-quotient-not-liftable`, which gives a
  concrete nonexact obstruction to naive GNS descent, already for `F_2`.
- `ideal-central-components-retain-an-amenable-nonqd-witness`, which splits a
  hypothetical counterexample along any ideal without assuming that QD traces
  form a face.
- `stw10-factorialize-amenable-nonqd-witnesses`, which uses the compact
  amenable-trace face to replace any counterexample by a separable factorial
  one.  In the exact case it sharpens this to a faithful amenable non-QD trace
  on a separable exact algebra whose GNS von Neumann algebra is `R`.  Exactness
  is essential for the hyperfinite-GNS conclusion.
