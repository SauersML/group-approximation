---
rg: 2
id: stw99-problem-ix1-nuclear-faithful-trace-quasidiagonal
kind: claim
title: Every separable nuclear C*-algebra with a faithful trace is quasidiagonal (STW Problem IX(1))
root: true
distinct_from:
  amenable-implies-operator-mf: that is the group case with the UCT available through Tu's theorem; this drops the UCT, which is exactly what remains after Tikuisis--White--Winter.
  stw99-problem-vii-blackadar-kirchberg: that assumes only stable finiteness; this assumes a faithful trace, which is stronger outside the simple case, so this is the easier special case (route stw99-vii-implies-ix1).
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem IX(1) of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026).**  Let `A` be a separable nuclear C\*-algebra with a
faithful trace.  Is `A` quasidiagonal?

Known with the UCT: Tikuisis--White--Winter (Ann. of Math. 185 (2017),
Theorem A) plus Blackadar--Kirchberg's NF characterization.  The repository
carries that route in Lean as `TikuisisWhiteWinterStatement UCT` and the
assembly `tikuisisWhiteWinterStatement_of_core`
(`GroupApproximation/Analysis/TikuisisWhiteWinterCore.lean`), with the Annals
theorem and Connes--Haagerup as typed literature inputs.  This problem is the
same statement with the `UCT A` binder removed.

In the repository's vocabulary the conclusion is `IsNFAlgebra A`
(Blackadar--Kirchberg: nuclear and quasidiagonal), so the statement reads

```text
∀ (A : Type u) [CStarAlgebra A], SeparableSpace A → IsNuclearCStarAlgebra A →
  (FaithfulTracialState A) → IsNFAlgebra A.
```
