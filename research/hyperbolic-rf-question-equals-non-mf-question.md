---
rg: 2
id: hyperbolic-rf-question-equals-non-mf-question
kind: claim
title: Some hyperbolic group fails residual finiteness exactly when some hyperbolic group fails MF
distinct_from:
  hyperbolic-rf-question-equals-vtf-question: that equates the residual-finiteness question with virtual torsion-freeness through Dehn filling; this equates it with the MF property through Kapovich--Wise, Olshanskii's common quotients and Ozawa--Thom
  mf-kazhdan-group-without-finite-quotients-is-trivial: that is one input, about Kazhdan groups in general; this is the existence equivalence for word-hyperbolic groups that it helps prove
---

The following existential assertions are equivalent.

1. Some word-hyperbolic group is not residually finite.
2. Some infinite word-hyperbolic group has no nontrivial finite quotient.
3. Some infinite word-hyperbolic Kazhdan group has no nontrivial finite
   quotient.
4. Some word-hyperbolic group is not MF.

Equivalently: every hyperbolic group is residually finite iff every
hyperbolic group is MF.  Gromov's question is therefore a question inside this
repository's MF program, and a counterexample may always be assumed to have
property (T) and no finite quotients at all.

Proof in `hyperbolic-rf-question-equals-non-mf-question-proof`.  Imported
inputs: Kapovich--Wise (J. Algebra 2000), Olshanskii's G-subgroup theorem
(IJAC 1993, read through Minasyan's verbatim restatement), Ozawa--Thom
(through Dadarlat), the existence of a torsion-free hyperbolic Kazhdan group,
and residually finite groups being MF.  No historical novelty is claimed for
the combination; the argument is supplied in full.  Not Lean-verified.

The same cycle is recorded route by route:
`quotientless-hyperbolic-via-kapovich-wise`,
`kazhdan-quotientless-hyperbolic-via-common-quotient`,
`non-mf-hyperbolic-from-kazhdan-quotientless`,
`non-rf-hyperbolic-from-non-mf-hyperbolic`, and the one-line
`non-rf-hyperbolic-from-quotientless-hyperbolic`.
