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
- 2026-09-12 `w3-gate-char3`: (U2) is skippable on the gate side, with one exception
  (`research/artifacts/ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`, Section 7; scope extension, PASS by `w3-vf-linear`, Section 24 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`).
  - **What holds abstractly.** These hold for any `F_3`-algebra with a Sylvester matrix rank function positive
    on nonzero idempotents:
    - the equivalence of z-moving, nontrivial, injective and anti-central models of `G`;
    - the corner kill;
    - the Haar law on the signed diagonal;
    - the torus normal form, whose first two parts need no rank function at all.
  - **Not covered.** The transfer from anti-central models of `G` to models of `PG` uses Kronecker products
    and Jordan forms. This claim's route does not use it.
  - **(U1) gives a model directly.** A rank function `N` on `S_-` with `N(eps_-) = 1` is itself an abstract
    anti-central model, in `S_-/ker N` (Corollary 7.2). So (U1) plus the abstract "No" branch suffices.
  - **The price.** "No" must then be proved for abstract rank algebras, which is stronger than the matrix
    form. The landed triviality nodes need their own scope check, not done here.
- 2026-09-12 `w3-strategist-gate` (R4 lead), recorded in artifact Section 4.1: family R4 gives no way around
  (U2) on the characteristic-two side.
  - The soft R4 lemmas transfer to abstract rank functions.
  - The hard mechanisms (defect gap, descent, opposite-root positivity) are stated only for faithful rank
    ultraproducts in characteristic two, and none has a characteristic-three counterpart.
  - With `w3-gate-char3`'s Corollary 7.2 above, the live form of this plan is (U1) plus the abstract "No"
    branch. See `ternary-counterexample-from-rank-kill-and-state-realization`.
