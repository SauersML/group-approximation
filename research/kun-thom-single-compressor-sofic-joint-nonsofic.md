---
rg: 2
id: kun-thom-single-compressor-sofic-joint-nonsofic
kind: claim
title: Every single positive Kun--Thom compressor action is sofic although the full multi-compressor coset action is nonsofic
distinct_from:
  coordinate-action-not-sofic: That is the established nonsoficity of the full Kun--Thom coset action; this claim locates the obstruction more sharply by proving every individual positive compressor restriction is sofic.
  commuting-sofic-actions-need-not-combine: That is a diagonal two-copy counterexample to GKP Question 4.2; this concerns the internal compressor geometry of the Kun--Thom coset action and compares one-compressor HNN subgroups with the full ambient group.
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

For the Kun--Thom polynomial/Laurent-polynomial pair, let `Gamma` be the
positive polynomial elementary subgroup and, for each positive elementary
monomial compressor `A_ij=I+E_ij`, let

`V_ij=<Gamma,t_ij>`

be the corresponding one-compressor ascending-HNN subgroup.  Then every
restricted coset action

`V_ij ↷ V_ij/Gamma`

is sofic, while the full Kun--Thom action

`G ↷ G/Gamma`

is nonsofic.

Thus the nonsoficity of the Kun--Thom coordinate action is a genuinely
**multi-compressor compatibility phenomenon**: it is not already visible in
any one positive ascending-HNN direction.

The normalized-HS consequence is equally sharp.
`kt-single-compressor-canonical-lamps-do-not-exactify-actor` applies GKP
wreath permanence to each one-compressor action and obtains canonical
permutation microstates of its binary wreath.  Their actor restrictions stay
a uniform distance, after negligible padding, from every exact
finite-dimensional actor representation.  Otherwise property `(T)` and
finite-dimensional commutant no-growth would collapse two canonically
separated coordinate lamps.  Hence even the full mixed Bernoulli trace for
one compressor does not supply actor exactification; only simultaneous
multi-compressor compatibility can possibly close the unitary route.
