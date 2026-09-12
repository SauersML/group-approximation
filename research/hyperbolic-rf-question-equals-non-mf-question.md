---
rg: 2
id: hyperbolic-rf-question-equals-non-mf-question
kind: claim
title: Proposed four-way equivalence for hyperbolic residual finiteness, torsion, Kazhdan quotients and MF
distinct_from:
  hyperbolic-rf-question-equals-vtf-question: that equates the residual-finiteness question with virtual torsion-freeness through Dehn filling; this equates it with the MF property through Kapovich--Wise, Olshanskii's common quotients and Ozawa--Thom
  mf-kazhdan-group-without-finite-quotients-is-trivial: that is one input, about Kazhdan groups in general; this is the existence equivalence for word-hyperbolic groups that it helps prove
artifacts:
  - research/artifacts/hyperbolic-four-statements-audit-2026-09-11.md
---

The following four-way equivalence is the **open target**, not an established
result under the operator-MF convention.

1. Some word-hyperbolic group is not residually finite.
2. Some word-hyperbolic group is not virtually torsion-free.
3. Some infinite word-hyperbolic Kazhdan group has no nontrivial finite quotient.
4. Some word-hyperbolic group is not operator MF.

The established part is [[hyperbolic-rf-vtf-kazhdan-equivalence]]: (1), (2),
and (3) are equivalent. Also (4) implies (1), because countable residually
finite groups are MF. The first three are equivalent to existence of an
infinite hyperbolic group without nontrivial finite quotients, without
requiring property (T) in that intermediate formulation.

## Attempts

The previous route treated an operator-MF Kazhdan group as weakly
quasidiagonal and applied Ozawa--Thom. The audit on 2026-09-11 found that
the cited proposition requires completely positive asymptotic maps, an
extra condition not supplied by an MF embedding. The printed introductory
arrow in the cited paper does not have the claimed proof from definitions.
Consequently [[mf-kazhdan-group-without-finite-quotients-is-trivial]] is an
open sufficient premise, and the old citation route cannot establish it.
This is a proof gap, not a refutation of the four-way target.

Two independent attempts to repair the bridge with hyperbolicity, finite
presentation, or property (T) found no usable theorem. Local lifting for the
full group C*-algebra and local operator-norm matrix stability are sufficient
extra hypotheses, but neither is proved for the constructed quotient.
The complete deductions and exact boundary are recorded in
`research/artifacts/hyperbolic-four-statements-audit-2026-09-11.md`.

The existing proof route is now explicitly conditional on the missing MF
premise. The existence assertions themselves remain open. No historical
novelty or Lean verification is claimed.
