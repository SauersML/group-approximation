---
rg: 2
id: houghton-ray-stabilizer-distortion-at-most-x-log-x
kind: claim
title: "For n >= 4 the one-ray stabilizer H_(n-1) is at most x log x distorted in H_n (three stacks sort in O(N log N)); for n = 3 it is quadratically distorted"
distinct_from:
  houghton-cohomological-dehn-lower-bounds-cap-at-quadratic: that bounds the distortion of abelian and central subgroups; this bounds the distortion of the non-abelian ray stabilizer H_(n-1).
  houghton-group-h3-has-at-least-cubic-dehn-function: its proof uses the quadratic distortion of H_2 in H_3; this shows the analogous subgroup for n >= 4 is distorted by at most a log factor.
---

Fix `n >= 4`. Let `K ≤ H_n` be the pointwise stabilizer of ray `n`. It is
the copy of `H_(n-1)` acting on rays `1..n-1`. Fix finite generating sets
`S_K` of `K` and `S ⊇ S_K` of `H_n`.

**Claim.** There is a constant `C` such that every `g ∈ K` satisfies

`|g|_(S_K) <= C (|g|_S + 1) log(|g|_S + 2)`.

So the distortion function `Dist_K(x) = max { |g|_(S_K) : g ∈ K, |g|_S <= x }`
satisfies `Dist_K(x) ≼ x log x`.

Refinement used downstream: every finitary permutation of rays `1..n-1`
supported in depth `<= D` has `S_K`-length `<= C (D + 1) log(D + 2)`. This
needs only that `K` has at least three rays.

For contrast, when `n = 3` the base `K = H_2` is quadratically distorted:
`h_(m-1) = Y^(m-1) X^(-m) Y^(-(m-1))` has `H_3`-length `<= 3m` and
`H_2`-length `>= (m-1) m` (Remarks of
`houghton-h3-at-least-cubic-dehn-corridor-proof`). The step that fails for
`n = 3` is merge sort, which needs three stacks. `H_2` has only two rays.

Whether the `log` can be removed is open. That would mean `K` is undistorted,
i.e. `n` stacks could be simulated on `n - 1 >= 3` stacks with constant
overhead on every finitary rearrangement.

## Attempts

- 2026-09-19 (swarm-0917-w14-w14-z-follow, host-geometry): proved in
  `houghton-ray-stabilizer-distortion-stack-sort-proof`. Machine-checked for
  `n = 4, 5` and depths `D <= 34` in
  `experiments/houghton-lid-transport-2026-09-17/check_lid_and_sort.py`.
