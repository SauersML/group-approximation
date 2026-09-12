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
- `diagonal-retention-fusion-coefficient` gives the exact categorical
  multiplicity: it is the infimum of the powered Gram quadratic form divided
  by the original Gram form over finite group-algebra vectors.  It tends to
  zero whenever the scalar-kernel quotient has CE canonical algebra.
- In particular, `regular-mixing-forces-diagonal-retention-decay` rules out
  the obvious scalar-kernel repair for every standard source currently in
  the graph: the free-group IRS, the sofic RACG BCS trace, and the CDI
  property-T lattice character.  Regular mixing makes the scalar kernel
  trivial but forces every retained fusion weight to vanish.  Leaving the
  character unmixed can evade this conclusion only when its scalar-kernel
  quotient is itself already non-hyperlinear.
- The apparent categorical escape `pi -> pi tensor pi tensor conjugate(pi)`
  is also quantitatively exhausted.  `pairwise-coevaluation-retention-has-commutant-density-decay`
  computes its weight as `(dim End_G(pi)/(dim pi)^2)^n`; it decays for every
  fixed nonscalar finite-dimensional type, while a diffuse factor GNS
  representation has no Hilbert-space coevaluation vector at all.  Any
  surviving fusion must therefore be a new global channel, not cancellation
  of representation/conjugate pairs.
