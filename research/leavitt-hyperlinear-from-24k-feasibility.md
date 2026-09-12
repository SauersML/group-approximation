---
rg: 2
id: leavitt-hyperlinear-from-24k-feasibility
kind: route
title: Read hyperlinearity of the unit group off vanishing of every 24k infimum
target: binary-leavitt-unit-group-hyperlinear
requires:
  - leavitt-24k-feasibility-vanishes
  - binary-leavitt-hyperlinear-iff-24k-feasible
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

The second prerequisite is the equivalence `(LK4)`, whose left-to-right
direction is exactly what is needed: vanishing of every `Delta_m` produces
models of the free product `P` that kill each fixed element of `ker q`
asymptotically, hence a homomorphism of `H` into the unitary group of a
tracial matrix ultraproduct, injective by simplicity and nontrivial because
`||C_k - I||_2 = sqrt 2`.  The uniform separation constant `1` is supplied
inside that criterion by the amplification `V -> (I (+) V)^(tensor r)`, so
nothing further is assumed here.

The route therefore adds no analysis of its own; its content is the first
prerequisite, which is open.  Note the payoff is one side of a fork: by
`hyperlinear-nonsofic-from-leavitt-unit-group` a positive answer produces a
hyperlinear nonsofic group, while the opposite branch
(`nonhyperlinear-from-leavitt-24k-gap`) closes the program goal instead.
