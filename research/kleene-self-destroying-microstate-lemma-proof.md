---
rg: 2
id: kleene-self-destroying-microstate-lemma-proof
kind: route
title: Apply the recursion theorem to the open microstate-search window
target: kleene-self-destroying-microstate-lemma
requires: []
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

Fix computable constants `delta_0,beta` strictly between the two pairs of
thresholds in the claim.  By the parameterized recursion theorem there is an
index `e` whose machine first computes the finite presentation and marked word
assigned to `e`, then enumerates dimensions and a computable dense family of
unitary tuples, halting when the strict inequalities `(KSD3)` are certified.

If the machine halts, the found tuple has relator defect below `delta` and mark
distance above `beta>alpha`, contradicting the compiler's halting soundness.
Thus it does not halt, and nonhalting completeness makes `w_e` nontrivial.

If `G_e` were hyperlinear, approximate trace-preserving representations of its
finite presentation would have relator defect tending to zero.  Since the
canonical group trace is zero on the nonidentity element `w_e`, their marked
distance tends to `sqrt(2)`.  One lies strictly inside `(KSD3)`.  Continuity
then gives a neighborhood inside the same window, which the dense effective
enumeration eventually visits.  That would halt the machine, the desired
contradiction.

