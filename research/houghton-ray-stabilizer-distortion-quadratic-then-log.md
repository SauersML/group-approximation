---
rg: 2
id: houghton-ray-stabilizer-distortion-quadratic-then-log
kind: claim
title: "H_2 is exactly quadratically distorted in H_3, and for 3 <= k < n the ray stabilizer H_k is at most x log x distorted in H_n"
distinct_from:
  houghton-word-length-is-complexity-up-to-log: that is the imported word-length estimate inside one H_n; this compares word lengths in a ray stabilizer and in the ambient group.
  houghton-group-h3-has-at-least-cubic-dehn-function: that proves a Dehn lower bound and uses only the lower half (quadratic distortion) of part (a); this pins the distortion from both sides.
---

For `n >= 3` and `1 <= k < n`, let `B_k ≤ H_n` be the pointwise stabilizer of
the rays `k+1, ..., n`. So `B_k ≅ H_k`. Fix finite generating sets `S_k` of
`B_k` and `S` of `H_n`, and put

`Dist_(k,n)(ℓ) = max { |b|_(S_k) : b ∈ B_k, |b|_S <= ℓ }`.

**(a) `k = 2`, `n = 3`.** `Dist_(2,3)(ℓ) ≃ ℓ^2`. Concretely, for
`X = λ_(1,2)`, `Y = λ_(1,3)`, `α = ((1,1),(1,2))`, `S_2 = {X, α}` and
`S = {X, Y, α}`:

- every `b ∈ B_2` with `|b|_S = ℓ >= 1` has `|b|_(S_2) <= 4(2ℓ+5)^2 + ℓ`
  (and in particular `B_2 = <X, α>`);
- `h = Y^(m-1) X^(-m) Y^(-(m-1)) ∈ B_2` has `|h|_S <= 3m` and
  `|h|_(S_2) >= m(m-1)`.

**(b) `3 <= k < n`.** `Dist_(k,n)(ℓ) ≼ ℓ log ℓ`.

Part (b) answers the question of Burillo–Cleary–Martino–Röver (whether `H_k`
is distorted in `H_n`, `3 <= k < n`) up to the logarithmic factor: the
distortion, if any, is at most logarithmic. Whether it is exactly linear stays
open.

Proof: `houghton-ray-stabilizer-distortion-proof`.
