---
rg: 2
id: finite-affine-profile-or-proof
kind: route
title: Narrow every question-pair predicate before dispatching to a linear PCPP
target: finite-affine-profile-or-removes-pcpp-section-gate
requires:
  - dfnqxy-mie-pcpp-has-no-global-affine-replacement
  - dfnqxy-answer-reduction-does-not-preserve-affine-safe-support
  - boolean-relations-have-affine-complete-rstar-pp-gadgets
  - finite-lcs-product-sign-is-exact-or
---

Enumerate every affine subspace `A_q subseteq C_q` at every sampled source
question pair and take the finite product of these choices.  The branch
`A_q=Aff(S_q)` contains the unknown affine-safe perfect support, while every
branch predicate is pointwise narrower than the source predicate.  For one
fixed branch and one fixed `q`, the two Hadamard words encoding `A_q` are
the solution set of affine equations.  Use the BSGH+05 linear-PCPP special
case there and dispatch on `q`; Figure 5 of DFNQXY gives the whole pair to
every player queried about the proof, so no cross-pair proof coherence is
required.  Pad the finitely many PCPPs to common lengths.

The affine proof encoder and affine checks make every positive local view
affine-safe.  Apply the affine-complete `R_*` gadget, enumerate its cap
profiles, and combine all source and cap profiles with the exact finite LCS
OR.  Pointwise narrowing, DFNQXY answer-reduction soundness, exact visible
projection of the pp gadgets, and selector-corner decoding give the four
successive soundness implications.  Every enumeration is finite and
effective for the fixed game, irrespective of its size.

