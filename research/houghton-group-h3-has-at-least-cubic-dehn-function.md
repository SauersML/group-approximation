---
rg: 2
id: houghton-group-h3-has-at-least-cubic-dehn-function
kind: claim
title: "Houghton's group H_3 has Dehn function at least cubic"
distinct_from:
  some-houghton-group-has-superquadratic-dehn-function: that asks only that some H_n fail a quadratic bound; this gives the explicit cubic lower bound for the single group H_3, which implies it.
  houghton-groups-have-at-least-quadratic-dehn-function: that is the x^2 lower bound for every n >= 3, from non-hyperbolicity; this is the strictly stronger x^3 bound for n = 3.
  houghton-group-h3-has-polynomial-dehn-function: that is an upper bound for H_3; this is a lower bound.
---

For every finite presentation of Houghton's group `H_3`, the Dehn function
satisfies `x^3 ≼ δ_(H_3)(x)`.

A witness family: with `X = λ_(1,2)`, `Y = λ_(1,3)` and
`α = ((1,1),(1,2))`, the null-homotopic words
`w_m = [Y^m X^m Y^(-m), α]` (`m >= 2`) have length `6m + 2` and area at
least `m^2 (m - 1)`.

## Attempts

- 2026-09-18 (swarm-0917-w13-w13-z-follow, minimal-counterexample): proved by
  the Y-corridor argument in
  `houghton-h3-at-least-cubic-dehn-corridor-proof`. The argument uses the
  ascending HNN structure `H_3 = H_2 *_φ` and the fact that `H_2` is
  quadratically distorted in `H_3`. The lower bound was machine-checked for
  `m <= 8` in `experiments/houghton-heisenberg-2026-09-17/corridor_lb.py`.
- 2026-09-19 (swarm-0917-w14-w14-z-follow, referee, verdict: survives).
  Independently checked every step of
  `houghton-h3-at-least-cubic-dehn-corridor-proof`. Two points were flagged
  for review, and both hold:
  - the orientation paragraph in Step 2b: the tangent rule gives opposite
    exponents on paired letters and puts both sides on the head or tail
    vertices;
  - case (ii) of Step 3: `α^(Y^m)` is a ray-3 transposition fixed by
    conjugation by `X^(±m)`, so after `Y^(-k)` it moves `(3, m-k)`.

  Also checked:
  - injectivity in 1b, via `τ`;
  - the Neumann reduction in 1c;
  - subadditivity of `inv` in 2a;
  - the arc lemma in 2c;
  - facts F1 and F2, and the forcing.

  The forcing step generalizes to `[Y^m u Y^(-m), α]` for every `u ∈ H_2`
  and to every `n`, re-checked for `n = 4, 5` in
  `experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.py`.
  For `n >= 4`, though, the certified value is only `O(x^2)`, and every
  corridor certificate is `O(x^2 log x)`; see
  `houghton-ray-stabilizer-corridor-bounds-cap-near-quadratic`. So the
  cubic bound is specific to `n = 3`, where the base `H_2` has two rays.
- 2026-09-19 (swarm-0917-w14-w14-z-follow, calibration/referee): independent
  hand referee of `houghton-h3-at-least-cubic-dehn-corridor-proof`; verdict
  survives. Checked: the HNN normal form and injectivity (1b), the Neumann
  finite subset (1c), the Step 2b orientation (paired letters have opposite
  exponents), the arc lemma (2c), (F2) `inv(h_k) = km`, and case (ii) (the arc
  `(X^(-m) α^(Y^m) X^m)^(Y^(-k))` moves `(3, m-k)`). Re-verified from scratch
  for `m = 2..12` (forced matching unique, cost `m^2(m-1)`) in
  `experiments/houghton-corridor-cap-2026-09-17/referee_and_cap.py`. Also
  showed that this method is exhausted at `x^3`:
  `houghton-hnn-corridor-lower-bounds-cap-at-base-distortion`.
