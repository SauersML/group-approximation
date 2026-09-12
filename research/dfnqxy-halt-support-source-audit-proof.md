---
rg: 2
id: dfnqxy-halt-support-source-audit-proof
kind: route
title: Track the existential strategy and witness choices in the two primary completeness proofs
target: dfnqxy-halt-completeness-support-is-not-canonically-specified
requires:
  - jnvwy-low-degree-pcp-reflects-affine-unsafety
  - dfnqxy-pcpp-contract-allows-nonlinear-proof-views
---

Read the quantifiers in DFNQXY Theorem 6.10 before attempting a support
enumeration.  Its starting protocol `V` is introduced existentially, and
each invocation of Theorem 6.2 concludes only existence of a value-one
strategy.  The proof refers to the JNVWY/Natarajan--Zhang completeness
construction rather than defining a joint proof-witness section.

Choosing JNVWY's HALT verifier does not remove this choice.  JNVWY Theorem
12.6 obtains the HALT strategy by Claim 12.7's downward existential
induction.  In the answer-reduction step, Theorem 10.25 selects satisfying
strings and certificate polynomials by existence, after which Section 10.6
postprocesses each source outcome with a selected proof.  The paper does not
give one simultaneous selection throughout the recursive strategy.

Thus the primary statements determine a nonempty set of possible
completeness strategies, not one positive-support table.  An affine-support
claim must add a quantifier or a section: construct one coherent safe chain,
prove all chains safe, or prove all chains unsafe.  The cited existence
theorem alone proves none of these.
