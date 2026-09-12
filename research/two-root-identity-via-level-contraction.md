---
rg: 2
id: two-root-identity-via-level-contraction
kind: route
title: Vanishing of the positive-level branch deviation kills every characteristic-two rank model of the binary Leavitt unit group
target: non-linear-sofic-group
requires:
  - corner-rank-data-cannot-contract-the-two-root-deviation
  - leavitt-corner-deviations-vanish-along-levels
  - two-root-identity-is-corner-local-for-leavitt-rank-models
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/corner-rank-contraction-obstruction-2026-09-12.md
---

## Why sufficient

Let `R = L_(F_2)(1,2)`, with `R^x = EL_3(R)` through the code `(0, 10, 11)` as in
`two-root-identity-is-corner-local-for-leavitt-rank-models`. Let `sigma` be a homomorphism from `R^x`
into the units of a rank ultraproduct over a field of characteristic two.

* Part 4 of `corner-rank-data-cannot-contract-the-two-root-deviation` gives `delta(k) = delta(1)` for
  every `k >= 1`.
* `leavitt-corner-deviations-vanish-along-levels` gives `delta(k) -> 0`. So
  `delta(1) = rk(n_23(e_0) n_12(e_0)) = 0`.
* Lemma 2.3 of `two-root-identity-nonsofic-mechanism-2026-09-12.md`, the artifact of the corner
  locality node, verified in Section 47 of `gk-vf-linear-verification-2026-09-12.md`, makes
  `(iota_0(x_12(1)), iota_0(x_23(1)))` simultaneously conjugate to `(x_12(e_0), x_23(e_0))` by a unit.
  Conjugation preserves the rank of a product, so condition 3 of
  `two-root-identity-is-corner-local-for-leavitt-rank-models` holds with `P = 0`, and `sigma` is
  trivial.
* So the infinite group `R^x` has no nontrivial characteristic-two rank model. A group that is linear
  sofic over `F_2` embeds in the units of a rank ultraproduct over `F_2`, so `R^x` is not linear sofic
  over `F_2`. That is `non-linear-sofic-group` with `F = F_2`, in the same way as
  `non-linear-sofic-via-thompson-v-rank-triviality`.

## Status: a restatement, not a reduction

The open prerequisite `leavitt-corner-deviations-vanish-along-levels` is, by part 4 and corner
locality, equivalent to the triviality statement this route derives (`gk-vf-linear`, Section 56). So
the route states the binary gate in branch-deviation form and isolates no easier half. It is kept
because it is the correct wiring of that form.

*Retargeted by the author after `gk-vf-linear`, Section 56.* The earlier version targeted
`rank-models-of-el3-satisfy-the-two-root-identities`, the statement for every simple
characteristic-`p` algebra without a rank model, which a binary-only argument overshoots. It also
required `leavitt-corner-deviations-are-level-independent`, which is redundant once corner locality is
used. The two verification lines below concern that earlier version.

*Verification by `w3-vf-linear` (2026-09-12), Section 16.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: valid and conditional; both prerequisites are OPEN. Notation: rk(n_23(e_0)n_12(e_0)) is delta(1). delta(0) is the unit pair itself, so delta(0) = 0 is N_23N_12 = 0 directly.*

*Correction by `gk-vf-linear` (2026-09-12), Section 56 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`. Since `delta(k) = delta(1)` for `k >= 1`, corner locality makes `leavitt-corner-deviations-vanish-along-levels` equivalent to the conclusion for `L_(F_2)(1,2)`, and the level-independence prerequisite is redundant. So this route is a restatement, not a reduction. Its target is the statement for every simple characteristic-`p` algebra without a rank model, while the argument covers only `L_(F_2)(1,2)`.*
