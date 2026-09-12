---
rg: 2
id: leavitt-two-root-defect-piece-forces-covariant-diagonal
kind: claim
title: A rank model violating the two-root identity carries a covariant cylinder diagonal on its defect piece
distinct_from:
  leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model: that shows the defect piece carries an injective rank model of the unit group and kills the fixed case; this asks for a covariant copy of the Leavitt diagonal on that piece
  thompson-v-cantor-system-has-no-covariant-rank-model: that is the halving obstruction for covariant cylinder idempotents; this supplies such idempotents from a violation of the identity
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)` and let `sigma` be a characteristic-two rank model of `R^x` with
`delta = rk(N'_23 N'_12) > 0` on the corner pair on `[1000]`. Then on the defect piece `Q`, or on a
nested piece, there are idempotents `e_w`, indexed by cylinders, such that:
- `e_(w0) + e_(w1) = e_w`, with the summands orthogonal;
- conjugation by prefix-replacing elements of `V` permutes them covariantly;
- some proper `e_w` has positive rank.

**Why it matters.** The halving obstruction then contradicts `delta > 0`. That proves the two-root
identity, so every char-2 rank model of `R^x` is trivial and `R^x` is not `F_2`-linear sofic.

## Attempts

- 2026-09-12 `w3-strategist-neg`, artifact Section 3.
  - **First lemma.** Root-group image spans `V_(w,w')` are covariant and refinement-stable, so refined
    images coincide up to rank zero, if the spans have ranks.
  - **Missing input.** Orthogonality of the `e_w`.
  - **Kill tests.** The join issue in rank ultraproducts; the Toeplitz Kazhdan violator
    `kazhdan-groups-without-fd-reps-violate-two-root-identity`, where the mechanism must fail.
- **Adversarial pass (w4-r4-adversary, artifact
  `research/artifacts/covariant-diagonal-plan-adversarial-audit-2026-09-12.md`).**
  - **Not refuted, but equivalent to the gate.** Covariant orthogonal cylinder idempotents are zero in
    every rank ultraproduct and every nonzero corner. So this claim's conclusion holds in no model, and
    the claim is the characteristic-two gate. Its route stays valid.
  - **The first lemma is inert.** By `covariant-monotone-cylinder-families-in-rank-models-are-constant`,
    every covariant, refinement-monotone family of principal ideals is constant, whatever the defect. The
    coincidence of refined root spans is an automatic instance, and since orthogonal families are
    monotone, "orthogonality" is the contradiction itself.
  - **Root spans carry only the known direction.** The all-coefficient identity on a frame `(a0, b, a1)`
    forces triviality, proved through a Weyl computation and simplicity, with no ring rank model.
  - **Kill tests.**
    - (a), joins, is not a kill: countable saturation gives joins and meets.
    - (b), the Toeplitz Kazhdan group, is consistent: its invariant trace forbids depth-changing units,
      so monotone families refine strictly there.
    - (c) is the gate itself.
  - **What a proof needs.** A rank-halving inequality between depths for some non-span piece built from
    the defect.
