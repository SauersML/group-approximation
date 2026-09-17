---
rg: 2
id: fpbs-finite-subgroup-classes-escape-q-lambda-orbits
kind: claim
title: For a finite nontrivial subgroup the infinite-intersection set is empty while subgroup classes have at least two points, so class-graph components escape the Q(Lambda)-orbits
invalidates: [fpbs-malnormal-subgroup-relations-finite-contacts-proof]
distinct_from:
  fpbs-malnormal-subgroup-relations-finite-contacts: that is the finite-contact obstruction whose item 3 places components of the infinite-contact class graph in <Q(Lambda)>-orbits; this is the counterexample to that sentence for finite nontrivial Lambda, which kills its proof route as written.
artifacts:
  - research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md
---

**ESTABLISHED.** Let `Gamma` be a countably infinite group with a free p.m.p. action `a` on `(X, mu)`, and let
`Lambda <= Gamma` be finite with `|Lambda| >= 2`. Put `I(gamma) = Lambda ∩ gamma^{-1} Lambda gamma` and
`Q(Lambda) = { gamma : I(gamma) infinite }`, as in `fpbs-malnormal-subgroup-relations-finite-contacts`.

Then `Q(Lambda)` is empty, so `<Q(Lambda)> = {e}` and the `<Q(Lambda)>`-orbit of every `x` is `{x}`. For
`S = E_{a|Lambda}` and any graphing, the component of the infinite-contact class graph through the class of `x`
contains the whole class `Lambda x`, which has `|Lambda| >= 2` points by freeness. So that component does not lie in
`<Q(Lambda)> x`. Step 5 of `fpbs-malnormal-subgroup-relations-finite-contacts-proof` ("a component lies in
`<Q(Lambda)> x`") and the first sentence of item 3 of the target fail as written.

The component does lie in `Lambda x` (artifact, Corollary 2, proof step 3). The repair is to state item 3 with
`<Q(Lambda) ∪ Lambda>`-orbits, or to assume `Lambda` infinite, where `Lambda ⊆ Q(Lambda)`.
