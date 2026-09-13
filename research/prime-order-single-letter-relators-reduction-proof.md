---
rg: 2
id: prime-order-single-letter-relators-reduction-proof
kind: route
title: Presentation argument for one-relator products with a single prime-order letter
target: prime-order-single-letter-relators-reduce-to-power-relators
requires: []
---

Let `A`, `H`, `α`, `p`, `W`, `G` and `R` be as in the claim, and write `W̄` for the image
of `W` in `R`.

**Step 1: add the power relator.** In `G`, `W = α^{-1}`, so `W^p = α^{-p} = 1`. Hence
`<<αW>> = <<αW, W^p>>` in `A * H`, and
`G = (A * H)/<<αW, W^p>> = (A * R)/<<α W̄>>`.

**Step 2: the order of `W̄`.** Since `W̄^p = 1` and `p` is prime, `W̄` has order `p` or `1`.

**Step 3: order `p`.** Then `α ↦ W̄^{-1}` is an isomorphism `<α> → <W̄>`, and the
presentation `(A * R)/<<α W̄>>` is by definition the amalgamated free product
`A *_{α = W̄^{-1}} R`. In an amalgamated free product both factors embed (normal forms),
so `A ≤ G` and `R ≤ G`.

**Step 4: order `1`.** Then `α W̄ = α` in `A * R`, so `G = (A * R)/<<α>> = (A/<<α>>) * R`.

**Step 5: triviality.**
- In case 3, `A` is nontrivial (it contains `α ≠ 1`), so `G ≠ 1`.
- In case 4, `G = 1` exactly when `A = <<α>>_A` and `R = 1`.
- `R = 1` forces `W̄ = 1`, so case 4 applies.

So `G = 1` if and only if `<<α>>_A = A` and `H = <<W^p>>_H`.

**Application.** For `H = B * C`, a cyclically reduced relator of `A * B * C` with exactly
one `A`-letter is conjugate to `αW` with `W ∈ B * C`. When every nontrivial element of `A`
has prime order and `A` is simple (as for `A_5`), `<<α>>_A = A` for every `α ≠ 1`, so
`A * B * C = <<αW>>` exactly when `B * C = <<W^p>>`, `p = ord(α)`.
