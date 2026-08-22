---
rg: 2
id: effective-fixed-density-diagonal-retention-character
kind: claim
title: An effective non-CE character has fixed-density self-retention along its polarizing tensor powers
---

Construct a finitely presented group `G` and a computable non-Connes-
embeddable character `tau` such that:

1. `H_tau={g:|tau(g)|=1}` is explicitly finitely normally generated;
2. for an explicit unbounded recurrence sequence `n_k`, the diagonal tensor
   character `tau^(n_k)` has a reducing summand of normalized character
   `tau` and trace weight at least one fixed `beta>0`.

Then `fixed-density-polarization-retention-is-terminal` applies to the
explicit finitely presented quotient `G/H_tau`.  The positive-kernel tests
`(FPR6)` are necessary conditions for every finite word list.

Literal independent-IRS intersection cannot supply this claim:
`irs-intersection-fixed-weight-retention-collapses` forces the IRS to be
deterministic.  A viable construction would therefore need genuinely
operator-algebraic fusion/self-similarity rather than retaining the original
IRS as a probability-measure component.

## Attempts

- Independent IRS intersections fail at the measure level: their laws
  converge to the Dirac mass at the almost-sure core, so a uniformly
  retained copy of the original law makes that law deterministic.
- A reducing corner of a diagonal tensor representation gives the exact
  convex decomposition `(FPR2)`.  Thus any recursive fusion proposal must
  pass all Gram-kernel inequalities `(FPR6)`; mere abstract isomorphism with
  the original algebra, without a trace-positive reducing projection, does
  not provide retention.
- If the polarized quotient is ICC, the domination theorem forces the
  retained character to equal the canonical quotient character.  Hence the
  only remaining attack is a nontrivial central decomposition or a direct
  construction whose conclusion is already the desired canonical non-CE
  summand.
