---
rg: 2
id: culf-mastel-rstar-halt-model-has-fano-cap-support
kind: claim
title: The halting Culf--Mastel R-star instance has a perfect CE model with Fano-cap local supports
distinct_from:
  culf-mastel-rstar-uniform-fano-cap-profile: that compiles all possible cap profiles into one marked LCS; this is now the sole source-specific existence statement needed for that finite compilation.
  rstar-fano-cap-support-preserves-nonru-affine-relaxation: that proves soundness after a cap profile is given; this asks whether the published completeness construction supplies such a profile.
---

OPEN.
Choose a perfect CE model in the halting branch of a realization of the
Culf--Mastel family over `R_*` such that, in every `R_*` context, its positive
joint spectral support becomes a Fano cap after translation by the ghost.

Equivalently, no local support contains all three points of a Fano line.
This must be checked in the actual perfect-completeness reduction to the
fixed language; NP-hardness of `R_*` alone does not preserve quantum support.
`culf-mastel-rstar-reduction-is-support-blind` verifies that Theorem 6.8
applies to `R_*` but that its stated classical extension map supplies no
no-Fano-line support conclusion.

## Attempts

- Pairwise arc pruning does not force the property: two equality-linked
  copies of the full seven-point relation are already a pruning fixed point.
- Passing to an extreme trace does not force it either; see
  `extreme-traces-and-local-pruning-do-not-select-fano-caps`.
- Minimal-support selection may shrink a particular satisfying face, but no
  theorem currently shows that a support-minimal perfect CE model of the
  Culf--Mastel instance cannot retain a forced Fano line.  This is the exact
  remaining possible canonical operation.
- On the finite-dimensional HALT strategy one may at least choose a
  support-minimal irreducible summand, by
  `finite-perfect-strategy-reduces-only-to-support-minimal-irrep`.  This
  minimizes only among central blocks of that representation; a simple block
  can retain every local atom, so the Fano conclusion still requires the
  source instance's overlap geometry.
- A constraintwise cap-range refinement of the classical NP reduction cannot
  solve the problem on a full nonaffine source support:
  `fano-cap-range-sections-cannot-encode-nonaffine-relations` would then turn
  the pp-gadget into an affine definition of that source relation.  Thus a
  positive result must use a proper support selected by the perfect trace or
  genuinely global contextual correlations.
- **The actual-support obstruction is now exact.**
  `fano-cap-witness-sections-force-source-affine-safety` traces the reverse
  homomorphism in Corollary 6.7 and proves that cap-supported witnesses for
  the positive source atoms force
  `Aff(S_i) subseteq C_i` in every source context.  A full-support
  one-in-three context fails because its affine hull adds `111`.  Constant
  answer size makes this condition finitely enumerable but does not imply it.
  The remaining positive possibility is therefore source-specific: prove
  that the particular HALT perfect strategy used before the NP reduction has
  affine-safe support in every answer and accepted-pair context.
- `dfnqxy-answer-reduction-does-not-preserve-affine-safe-support` audits the
  preceding Hadamard answer reduction.  All of its equality and code/subset
  tests are affine-safe; only the PCPP `Verify` views remain.  A three-outcome
  perfect EPR strategy gives an explicit counterexample showing that the
  transformation does not preserve affine safety in general.  Thus the
  cited perfectness/oracularizability argument cannot close this node: one
  must inspect the particular HALT strategy's positive PCPP view images.
- The alternative Lemma-20 source in
  `cmps-two-oracular-rstar-lift-has-commuting-context-stars` closes the
  mutual-neighbor hypothesis: its `2`-oracularizable completeness strategy
  survives a fixed-language `R_*` lift with jointly commuting incident
  context algebras.  This enables joint pruning, but does not itself exclude
  a full seven-point support or prove the affine-safety condition above.
