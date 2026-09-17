---
rg: 2
id: thompson-f-is-not-hyperlinear
kind: claim
title: Thompson's group F is not hyperlinear
refuted_by:
  - thompson-f-is-hyperlinear
distinct_from:
  thompson-f-is-not-sofic: that is the Hamming statement, implied by this one.
  thompson-v-not-hyperlinear: that is nonhyperlinearity of V, implied by this one because F <= V.
---

**OPEN.** Thompson's group `F` admits no injective homomorphism into a tracial matrix ultraproduct.

**Equivalent form** (`thompson-f-hyperlinear-iff-relator-system-hs-unstable`): unitary almost-solutions
of the two relators of `F` almost commute, uniformly in the dimension.

## Attempts

- **Kazhdan mechanisms.** No instance: `F` has the Haagerup property
  (`a-t-menable-groups-have-no-rigid-compression-defect`).
- **Uniform stability.** Fournier-Facio--Rangarajan (arXiv:2301.03970) prove uniform stability of `F`
  for submultiplicative norms. That controls uniform defect, not the pointwise normalized-HS defect
  statement 3 needs.
- **Entropy-measure transplant: every counting tool stops at nonsoficity** (lane
  swarm-0917-w2-nh-pull-1, 2026-09-17). Dead as a route to this claim; the exact split is recorded as
  `thompson-f-not-hyperlinear-via-nonsoficity-and-frames`.
  - **Invariant.** The input of each tool is a finite set with an approximate action: a sofic
    approximation or model space counted in Hamming measure. This covers sofic entropy and covering
    exponents, Rokhlin-entropy maximality (`maximal-bernoulli-rokhlin-entropy-makes-groups-uqs`),
    cellular-automaton and quantum cellular automaton surjunctivity (`sofic-groups-are-qca-surjunctive`),
    and Kun--Thom nonsofic actions (`groups-containing-kun-thom-pair-have-nonsofic-actions`). A unitary
    microstate yields such a set only through a basis that each `U_g` approximately permutes.
  - **Dying step.** Coupling one frame across the non-commuting generators `a, b`. For `F` nothing is lost
    in the permutation skeleton: monomial HS models have abelian normal soft kernel
    (`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`, clause 3), and every nontrivial normal
    subgroup of `F` contains the nonabelian `F'`. So frames for `F` are equivalent to soficity of `F`, and
    the transplant proves at most `thompson-f-is-not-sofic`. The missing step is exactly
    `thompson-f-hyperlinear-models-normalize-a-full-masa`, the frame problem at `F`. Exact
    finite-dimensional models are jointly diagonalizable, since `Rep_n(F) = Rep_n(Z^2)`, but they are not
    regular.
  - **Kun--Thom instance.** This needs an infranormal, non-normal pair of Kazhdan subgroups. `F` is
    Haagerup (`a-t-menable-groups-have-no-rigid-compression-defect`), so its Kazhdan subgroups are finite,
    and torsion-free, so they are trivial. The tool has no instance inside `F` at all.
  - **Action-level versions.** A non-embeddable Bernoulli crossed product `L^∞(X) ⋊ F` does not imply
    that `F` is non-hyperlinear, because it contains `L(F)` rather than embedding into it. The only
    permanence in the other direction, `gkp-connes-embeddable-generalized-wreath-permanence`, needs a sofic
    action, and for Bernoulli shifts that again needs soficity of `F`.
  - **Covering entropy.** It has no threshold short of emptiness of the microstate space
    (`atlas-entropy-and-cmi-stop-at-face-emptiness`), which is this claim itself.
  - **Calibration.** Spatial permutation models that follow `F` on `[0,1]` almost commute
    (`thompson-f-spatial-permutation-models-almost-commute`). So the natural geometric frame is
    degenerate, consistent with the dying step.
