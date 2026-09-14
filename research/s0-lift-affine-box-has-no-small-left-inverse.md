---
rg: 2
id: s0-lift-affine-box-has-no-small-left-inverse
kind: claim
title: No lift of s0 in a nine-dimensional affine box of the ternary anti-central summand has a left inverse supported on the radius-three mix2 ball
distinct_from:
  ternary-anti-invariant-swap-corner-is-full: that is the open corner equation, equivalent to a failure of direct finiteness of S_-; this excludes one finite family of witnesses of the sufficient condition (V3*) and decides nothing.
artifacts:
  - research/artifacts/gk3-ternary-bilinear-2026-09-14.md
  - experiments/gottschalk-ternary-corner/bscreen.py
---

**ESTABLISHED (computer-assisted, unreviewed).** Let `R = L_(F_3)(1,2)`, `G = R^x`, `S_- = F_3[G]/(1 + [z])` with
`z = -1`, `pi : S_- -> R` the evaluation, and `P` the level-two unitriangular 3-group (order 729).

- `alpha0 = 2[A] + 2[A D] + 2[A'] + [A' D]` is the support-four lift of `s0`, where `A = (0,10,11) -> (00,01,1)`,
  `A' = (00,01,1) -> (00,1,01)` and `D = diag(1,-1)`.
- `B` is the ball of radius two in `G` for `mix2 = {A, A', W, D, sigma_00, sigma_01}`, which has 38 elements up to
  sign, and `k_1, ..., k_9` is a basis of `ker pi ∩ span(B)`.
- `C_3` is the mix2 ball of radius three, which has 147 elements up to sign.

Claim: for every `lambda in F_3^9`, the lift `alpha = alpha0 + sum lambda_i k_i` of `s0` admits no `beta in span(C_3)`
and `n` with

    beta alpha = eps_- + n,     n in span{[p] - 1 : p in P}.

**Scope.** Each such solution would be a left inverse of a lift of `s0`, condition (V3*) of
`research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md`, hence a direct-finiteness failure of
`F_3[G]` and a strict linear automaton over `G`. The claim excludes only this finite family. It strictly contains
the single-lift slices of `gk3-ternary-fullness` whose lift lies in the box. Witnesses are expected to need deep
supports, so its evidence value for the open corner claim is low. Larger supports (the radius-four ball, and the
Klein-multiplied ball of Lemma 2.1 of the artifact) are recorded in the artifact as they complete.

Proof: `s0-lift-affine-box-left-inverse-census-proof`.
