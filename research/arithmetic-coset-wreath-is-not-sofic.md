---
rg: 2
id: arithmetic-coset-wreath-is-not-sofic
kind: claim
title: The summit arithmetic coset wreath is not sofic
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  wreath-not-sofic: that is the ESTABLISHED nonsoficity of the Kun-Thom wreath over their infranormal EL_r pair, by Kun-Thom Theorem A; this asks the same conclusion for the arithmetic wreath W_3, where Theorem A provably does not apply (arithmetic-integral-subgroup-is-incompressible), so a compression-free mechanism is required.
  dyadic-bruhat-tits-vertex-action-is-sofic: that conjectures the POSITIVE side at SL_2 - soficity of the dyadic vertex action; this is the negative side at SL_3 for the full wreath; the two record the fork's opposite polarities on neighbouring objects.
---

Claim (OPEN): `W_3 = (direct_sum_{Gamma/Lambda} C_2) rtimes Gamma`,
`Gamma = SL_3(Z[1/3])`, `Lambda = SL_3(Z)`, is not sofic.

Why it is open and not a corollary:
`arithmetic-integral-subgroup-is-incompressible` shows `Lambda` has
trivial compression semigroup in `Gamma`, so the Kun-Thom machinery
(Theorem A, Theorem C, Corollary D — all requiring infranormality)
cannot decide either `W_3`'s soficity or the soficity of the coset
action.  No other known nonsoficity mechanism applies: the
Chapman-Peled cocycle-stability engine is conditional and hyperbolic;
the LERF criterion (all actions of LERF groups are sofic) only shows
`Gamma` is not LERF, which was known.

Stakes.  Together with `coset-wreath-is-hyperlinear` this claim would
establish the off-goal separation root `hyperlinear-nonsofic-group`
(route `separation-from-nonsofic-hyperlinear-wreath`), so the p = 3
summit fork is WIN-WIN ACROSS BOTH ROOTS once this claim is settled
affirmatively: the collapse/entropy branch gives the main goal, the
construction branch gives the separation.  Settled negatively (`W_3`
sofic), it would give the first sofic wreath over a non-amenable
non-coamenable stabilizer — refuting the expectation that KT-style
obstructions are about the coset structure rather than compression per
se, and (by soficity implies hyperlinearity) it would ALSO establish
`coset-wreath-is-hyperlinear`, killing the collapse and excess-entropy
routes while resolving their fork.

## Attempts

- **Kun-Thom transplant: blocked.**  Theorem A's proof runs the
  compression semigroup through the sofic approximation to normalize
  the centralizer; with `P_Lambda = N(Lambda)` there is nothing to run.
  Any proof here must find a different finite-model obstruction.  The
  candidate raw material: Margulis normal subgroups + CSP make every
  finite `Gamma`-action factor through congruence quotients on which
  `Lambda` SURJECTS, so every finite equivariant quotient of the coset
  space is a point — the coset Schreier graph has no finite equivariant
  approximations at all.  Soficity of the ACTION, however, needs only
  almost-equivariant partial permutation models, which this does not
  yet exclude; the gap between "no finite equivariant quotients" and
  "no sofic approximation" is exactly where a proof must live, and
  property (T) is available to rigidify almost-actions.
- **Positive side (deliberately recorded).**  At SL_2 a peer lane
  (`dyadic-bruhat-tits-vertex-action-is-sofic`,
  `dyadic-random-lifts-produce-sofic-vertex-action`) attempts sofic
  models of the vertex action from random lifts of the two modular
  vertex actions with Bass-Serre separation.  If that construction
  works at SL_2 it likely adapts to SL_3 coset actions, and soficity of
  the coset action plus lamp bookkeeping would put `W_3` within reach
  of soficity itself — settling this claim negatively.  Watch that lane
  before investing in either polarity.
