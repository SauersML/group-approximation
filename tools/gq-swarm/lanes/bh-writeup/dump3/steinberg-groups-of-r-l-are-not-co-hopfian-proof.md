---
rg: 2
id: steinberg-groups-of-r-l-are-not-co-hopfian-proof
kind: route
title: The twist kernel is the stabilization kernel, which vanishes; the image misses the f-half of the last coordinate; isometries act trivially on stable K_2
target: steinberg-groups-of-r-l-are-not-co-hopfian
requires:
  - leavitt-stabilization-kernels-are-one-step
  - leavitt-surjective-k2-stability-implies-injective
  - leavitt-resolvent-k2-stability-holds
---

**Item 1.**
- `ker Σ^(e) = U_N` (`leavitt-stabilization-kernels-are-one-step`, item 3), and `U_N = 1`
  (`leavitt-resolvent-k2-stability-holds`, item 2). So `Σ^(e)` is injective.
- **Not surjective.** The image of `Σ^(e)` lies in `H_(ee*)`. Every element of `H_(ee*)` maps to a matrix fixing the vector
  `b_N ff*`, because the generators do: the column coefficients `a` satisfy `a ff* = 0`, and the row generators do not
  touch `b_N ff*`. But `φ(X_1N(1)) = t_1N(1)` sends `b_N ff*` to `b_N ff* + b_1 ff* != b_N ff*`. So `X_1N(1)` is not in the image.

**Item 2.**
- `Φ = Σ^(e)_1 ∘ ... ∘ Σ^(e)_N`, the twists at each coordinate. Each `Σ^(e)_k` is `Σ^(e)` conjugated by a Weyl word, so
  it is injective by item 1.
- Hence `Φ` is injective. Its image lies in the image of the outermost twist `Σ^(e)_1`, a proper subgroup by the argument of item 1 at
  coordinate `1`.

**Item 3.**
- **`Σ^(e)`.** `K_2(N, R_L) = S = {{λ, N+1}_N}` (`leavitt-resolvent-k2-stability-holds`, item 2). `S` is written on coordinates
  `1, 2 < N`, so `Σ^(e)` fixes it pointwise. The same holds for the whole copy of `St_(N-1)` on coordinates `1, ..., N-1`.
- **`Φ`.** `Φ` maps `K_2(N)` into `K_2(N)`. For `x in K_2(N)`, the stable class of `Φ(x)` is that of `x`. The composite
  `R -> e R e* -> R` induces the identity on `K_2(R)`: it is the corner isomorphism onto the full corner `ee* R ee*`,
  followed by the corner inclusion, and together these are conjugation by the isometry `e`. By injective stability,
  `Φ(x) = x`.
- So every `Σ^(e)^k(St_N)` contains `K_2(N)` and the copy of `St_(N-1)`, and every `Φ^k(St_N)` contains `K_2(N)`.
