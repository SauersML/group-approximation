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
  - GroupApproximation/Manuscript/NinetyNineProblems/StablyFinite.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw09-ix1-separating-mf-traces-audit-2026-08-30.md
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

Lean statement: `NinetyNineProblems.ProblemIX1Statement`
(`GroupApproximation/Manuscript/NinetyNineProblems/StablyFinite.lean`).

**Unconditional MF-trace subclass.**
`stw09-jointly-faithful-mf-traces-force-mf` proves that a separable unital
C-star algebra is MF whenever its MF tracial states jointly detect every
nonzero element.  Nuclearity then makes it quasidiagonal.  In particular,
IX(1) has a positive answer when the given faithful trace belongs to the
weak-star closed convex hull of the MF traces.  The proof selects finitely
many trace models to norm each prescribed finite packet and block-sums their
far-out coordinates; it uses neither the UCT nor Problem VII or X(1).

**Unconditional quasidiagonal-extension subclass.**
`stw09-local-mf-corner-traces-across-qd-extension-force-qd` gives a distinct
local-to-global criterion.  Suppose an ideal `I` has an increasing
quasicentral approximate unit of projections `(p_n)`, the normalized
restrictions of the given faithful trace to every nonzero corner
`p_n A p_n` are MF traces, and `A/I` is quasidiagonal.  Faithfulness makes
each corner algebra MF; nuclearity makes it quasidiagonal.  Compression to a
large `p_n` and the quotient map then give two u.c.p. matrix blocks which
together recover the ambient norm.  The corner traces need not extend
tracially to `A`, so this case is not a reformulation of the weak-star
closed-convex-hull criterion for ambient MF traces.
