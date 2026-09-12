---
rg: 2
id: ternary-anti-central-states-force-nontrivial-rank-models
kind: claim
title: A state on the anti-central summand of the ternary Leavitt group algebra forces a nontrivial characteristic-three rank model
distinct_from:
  anti-central-state-obstruction-equals-stable-finiteness: that shows a state exists iff the unit class is not nonpositive; this asks that any such state come from, or force, a rank model of the unit group
  ternary-leavitt-rank-models-move-z-iff-nontrivial: that identifies the kinds of rank model with one another; this is the upgrade from abstract K_0 states to rank models
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x` and `S_- = eps_- F_3[G]`. If `(K_0(S_-), [eps_-])` has a state,
then `G` has a nontrivial homomorphism into the units of a rank ultraproduct of matrix algebras in
characteristic three.

**Why it matters.** Together with the "No" branch of
`ternary-leavitt-units-have-a-nontrivial-char-three-rank-model`, it gives `k[eps_-] <= 0`, which refutes
Gottschalk on `G_3`. Proofs of rank triviality would then produce a counterexample instead of only
non-linear-soficity.

**Two steps.**
- (U1) A state gives a Sylvester matrix rank function on `S_-`. For regular rings this is Goodearl's
  correspondence with pseudo-rank functions.
- (U2) A rank function gives a matrix rank model. This step can be skipped if the gate proofs hold for
  abstract rank functions.

## Attempts

- 2026-09-12 `w3-strategist-neg`: proposed in artifact Section 2. First lemma: a `K_0`-order-embedding
  into a regular ring, for instance by universal localization. First kill test: a ring with the rank
  condition but no Sylvester matrix rank function.
