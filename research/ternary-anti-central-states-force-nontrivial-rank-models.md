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
- 2026-09-12 `w4-upg-audit` (`research/artifacts/rank-gate-axiom-audit-2026-09-12.md`): a scope check of the landed triviality tools.
  - **Class A (Sylvester axioms only).** Theorems A and D.2 of the two-root artifact, Propositions 6 and 8 of the rank-ring rigidity artifact, corner locality (`corner-defect-killing-rank-functions-are-augmentation`), the Toeplitz total-rank bound, the reversed-root identity, and the characteristic-three results scoped by `w3-gate-char3`.
  - **Class A' (faithful von Neumann regular rank rings).** The hard characteristic-two mechanisms are no longer confined to rank ultraproducts: `leavitt-defect-descent-chain-holds-in-regular-rank-rings` proves the defect piece, the gap, the descent and near-minimal multiplicativity for every faithful regular rank ring, through `regular-rank-ring-compressors-conserve-fixed-right-ideals` and ultraproducts of such rings. What still separates them from the abstract rank algebras of Corollary 7.2 is regularity of the quotient, not matrix approximation.
  - **What (U1) would then have to deliver** for a descent-type "No": a regular envelope of the rank function it produces (binary analogue: `sylvester-rank-functions-on-leavitt-units-are-regular`), or a class-A argument in which compactness of the space of rank functions replaces ultraproducts (`sylvester-rank-functions-have-a-uniform-two-root-defect-gap`). No characteristic-three descent exists yet.
  - **Matrix-only steps, used by no "No" argument:** tensor degrees other than `(1,0)` in fixed-ideal conservation, the transfer to `PG`, and the construction-side level normal forms.
- 2026-09-12 `w4-upg-kill`: kill test of (U1) (`research/artifacts/state-upgrade-kill-test-2026-09-12.md`).
  - **Criterion.** A ring carries a Sylvester matrix rank function iff no `I_(q+1)` lies below `I_q`
    through minors and triangular moves (`sylvester-rank-functions-iff-no-triangular-certificate`). With
    minors alone the criterion is the rank condition, equivalent to a state. So (U1) is exactly the
    flattening of triangular identity certificates to minor certificates.
  - **Over `S_-`.** Abstract "No" is a finite triangular certificate over `S_-`; the full corner is a
    finite minor certificate. (U1) for `S_-` is `anti-central-triangular-certificates-flatten-to-minors`
    (OPEN), the general upgrade `rank-condition-rings-carry-sylvester-rank-functions` (OPEN).
  - **Result.** No ring with the rank condition and no rank function was found. Split chains and idempotent
    triangular steps flatten (`split-identity-minors-survive-triangular-moves`), so a calibration ring
    needs a non-idempotent triangular step at a mixed minor. Regular rings satisfy (U1) by Goodearl
    (literature, not re-read), but a regular target for `S_-` with the rank condition would already kill
    the corner.
- 2026-09-12 `w4-upg-state` (`research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md`): step (U1) reduced to one open half.
  - **(U1a), proved.** A state on `K_0(S_-)` gives a nonzero weakly finite quotient `W`, all of whose states
    are faithful on idempotents, with `G_3` embedded and `z -> -1`.
    - Nodes: `anti-central-rank-condition-gives-weakly-finite-image`, from the general
      `rank-condition-rings-have-weakly-finite-images`.
    - Method: killing class-zero idempotents keeps the rank condition by an explicit retract, then Zorn.
    - In the certificate language above, weak finiteness is the part of (U1) that minor certificates
      already control.
  - **(U1b), open.** `anti-central-weakly-finite-images-carry-rank-functions`: flattening triangular
    certificates on `W`.
    - A state pins ranks of regular elements only. The free data is the Jordan types of order-three
      unipotents, which are the root elements (`rank-functions-extending-a-state-are-pinned-on-regular-elements`).
    - Kill test: a weakly finite `W ⊇ M_4(K)` with faithful states and `u^3 = 0`,
      `L u R = diag(1,1,1,0)` has no rank function.
  - **Rank-free counterexample criterion.** The corner is full iff no quotient of `F_3[G_3]` with `z = -1` is
    weakly finite (`ternary-anti-central-summand-has-no-weakly-finite-image`). A "No" argument using only
    weak finiteness bypasses U1 and U2 entirely.
