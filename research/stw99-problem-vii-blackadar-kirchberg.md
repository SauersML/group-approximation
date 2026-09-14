---
rg: 2
id: stw99-problem-vii-blackadar-kirchberg
kind: claim
title: Every separable nuclear stably finite C*-algebra is quasidiagonal (STW Problem VII, Blackadar--Kirchberg)
root: true
refuted_by: [blackadar-kirchberg-counterexample-exists]
distinct_from:
  kun-thom-wreath-stably-finite: that establishes stable finiteness of one group algebra; this asks whether stable finiteness forces quasidiagonality across all separable nuclear algebras.
  non-hyperlinear-group: that asks for a group whose von Neumann algebra escapes R^ω; this is the nuclear quasidiagonality question, whose non-nuclear analogue is already refuted by MIP*=RE.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/StablyFinite.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

**Problem VII of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902 (v2, addenda through April 2026)** (Blackadar--Kirchberg, Math. Ann. 307 (1997),
Question 7.3.2).  Is every separable nuclear stably finite C\*-algebra
quasidiagonal?

Context recorded by STW: the non-nuclear version is false.  MIP\*=RE
(Ji--Natarajan--Vidick--Wright--Yuen) gives a separably acting II₁ factor `M`
not embeddable in `R^ω`; a strongly dense separable C\*-subalgebra of `M` with
unique trace is stably finite but not `Q^ω`-embeddable, hence not MF and not
quasidiagonal.  So the problem is genuinely about nuclearity.

Special cases: Problem IX(1) (faithful trace) and, for group algebras, the
Rosenberg conjecture, now Tikuisis--White--Winter's Theorem C.  Faithful
traces force stable finiteness, so this problem implies IX(1)
(`stw99-vii-implies-ix1`).

A new positive permanence class is recorded in
`stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness`.  A pullback of
two separable nuclear quasidiagonal algebras is again separable, nuclear, and
quasidiagonal whenever one structure map is surjective, and is therefore
stably finite.  The coordinate embedding into the direct sum carries
quasidiagonality, while the surjection supplies the extension used for
nuclearity.  Iterating gives finite recursive pullbacks, and the leaves may
mix traceless solved pieces with faithful-trace UCT pieces.  This is not
general extension permanence: the second coordinate is essential to norm
detection.

There is also a quotient-separation theorem with no finite ideal-lattice
hypothesis.  `stw07-primitive-mf-traces-force-quasidiagonality` proves that
faithful MF traces on all primitive quotients pull back to a jointly faithful
family on `A`; finite direct sums of their matrix coordinates then make `A`
MF.  Hence a separable unital nuclear algebra is quasidiagonal whenever all
of its primitive quotients carry faithful traces and satisfy the UCT.  This
fibrewise trace hypothesis is stronger than stable finiteness of `A`; no
false quotient permanence for stable finiteness or faithful traces is used.

**Extension case and the K_0-Hahn--Banach property (2026-09-11).**  The
special case `blackadar-kirchberg-for-uct-quotient-extensions` (route
`bk-uct-extensions-from-problem-vii`) is equivalent, through
`brown-dadarlat-qd-extensions-and-k0-hahn-banach`, to the universal
K_0-Hahn--Banach property.  That property now splits into three parts:
- killing classes that change sign on quasidiagonal traces is established
  (`stw07-sign-changing-qd-trace-values-kill-class`);
- a singular class is never strictly one-signed on all traces
  (`stw07-singular-classes-change-sign-or-sit-on-boundary`);
- classes that vanish on a trace with a UCT kernel quotient seeing them
  rationally are killed (`stw07-quotient-trace-zero-nontorsion-class-is-killed`).

But `stw07-trace-invisible-classes-carry-hahn-banach` shows that stabilized
unitization makes every class trace-invisible, so the property is exactly a
question about trace-invisible classes.

On the negative side, the negation root
`blackadar-kirchberg-counterexample-exists` has the explicit mechanism
`stw07-qd-trace-positive-class-kills-qd-extension`.  Any algebra feeding it
must carry a nonquasidiagonal trace and a non-UCT nuclear quotient
(`stw07-trace-obstruction-forces-nonqd-trace-and-non-uct`).

Lean statement: `NinetyNineProblems.ProblemVIIStatement`
(`GroupApproximation/Manuscript/NinetyNineProblems/StablyFinite.lean`).
