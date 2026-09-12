---
rg: 2
id: leavitt-unit-group-algebra-is-directly-finite
kind: claim
title: The modular group algebra of the Leavitt unit group is directly finite
refuted_by:
  - leavitt-unit-group-algebra-not-directly-finite
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that is the negative root, a Kaplansky counterexample; this is its negation, the positive Kaplansky statement for this one group, and each refutes the other.
  leavitt-stable-finiteness-equals-direct-finiteness: that is the established equivalence of the scalar and matrix questions for this algebra; this asserts the positive answer to both.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

**OPEN.** In `S = F_2[R^x]`, `R = L_(F_2)(1,2)`, every `a, b` with `b a = 1`
satisfy `a b = 1`.

Payoffs:

* **Stable finiteness.** By `leavitt-stable-finiteness-equals-direct-finiteness`,
  `M_n(S)` is directly finite for every `n`.
* **Linear Gottschalk case.** Every injective `F_2`-linear cellular automaton
  over `R^x` is surjective. So the linear route
  `nonsurjunctive-from-stable-finiteness-failure` into
  `leavitt-unit-group-nonsurjunctive` is dead.
* **Kaplansky for the first nonsofic group.** It is the first positive answer
  for a group outside every approximation class known to force it.

It is not a proof that `R^x` is surjunctive, since nonlinear automata remain.

## Attempts

* **Split into the two normal forms.** By
  `leavitt-inverse-defects-are-visible-or-invisible`, it suffices to kill the
  visible problem (`no-left-invertible-lift-of-s0-in-leavitt-group-algebra`)
  and the invisible one (`leavitt-evaluation-kernel-unitization-directly-finite`).
  Route: `leavitt-direct-finiteness-from-both-lifting-problems-failing`.
* **Additive projective invariants.** Dead as a complete method. Every inverse
  defect has zero class in K_0, and so zero lifted trace at every precision
  (notes/KAPLANSKY_FULL_PROOF_GAP_AUDIT_2026-09-07.md, Section 2). A proof needs
  a non-stable invariant faithful on nonzero projectives, such as a faithful
  Sylvester rank function.
* **Soficity or linear soficity.** Not available: `R^x` is nonsofic
  (`openai-leavitt-unit-nonsofic`), and its linear soficity is open.
