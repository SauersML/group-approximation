---
rg: 2
id: minimal-cantor-z-no-f2-z2-via-point-column
kind: route
title: A Laurent ring in two variables would act faithfully on one orbit column of length 2mn+1 while needing about n^2 dimensions, so LC(X,F_2) ⋊ Z contains no F_2[Z^2] for any compact X
target: minimal-cantor-z-crossed-products-contain-no-f2-z2
requires:
  - steinberg-ore-domains-have-faithful-point-columns
---

Compared with `spectrally-complete-tuples-bound-commutative-rank`, this route needs no spectrally complete
element: it uses only that the image is a commutative domain. Compared with
`algebraic-core-gradings-bound-homogeneous-laurent-rank`, it covers every compact `X` and every element, not
just the odometer and homogeneous units.

This route proves the target in the stronger form: for every compact Hausdorff space `X`, every
homeomorphism `T` and every field `k`, there is no injective algebra homomorphism, unital or not,
`k[x^(±1), y^(±1)] → A = LC(X, k) ⋊_T Z`. Minimality, freeness and total disconnectedness of `X` are
not used, and neither is `k = F_2`.

## Proof

It is Part 5 of `steinberg-ore-domains-have-faithful-point-columns` with `P = Z`, generating set
`{±1}` and `D = 1`. It is spelled out here so that the constants can be checked.

1. **The image is Ore.** Suppose `ψ : k[x^(±1), y^(±1)] → A` is injective. Its image `C` is a
   nonzero commutative domain. For nonzero `a, b ∈ C` we have `ab = ba ∈ Ca ∩ Cb`, and `ab ≠ 0`. So
   `C` is a left Ore domain.
2. **A finite generating set with bounded support.** Put `S = {ψ(1), ψ(x), ψ(x^(-1)), ψ(y), ψ(y^(-1))}`,
   where `ψ(1)` is the idempotent unit of `C`. Each element of `A` is a finite sum `Σ_p f_p v_p`, so
   there is `m >= 1` with `|p| <= m` for every `p` in the support of every element of `S`.
3. **Growth of the source.** Let `V_n(S)` be the span of all products of between `1` and `n` elements
   of `S`. Since `ψ(1)` is a unit for `C`, `V_n(S)` contains `ψ(x^a y^b)` for every `(a, b)` with
   `|a| + |b| <= n - 1`. These are linearly independent because `ψ` is injective. Their number is
   `2(n-1)^2 + 2(n-1) + 1 >= n^2` for `n >= 2`.
4. **The point-column bound.** Part 3 of the lemma (whose proof uses Part 2, the faithful column
   `c ↦ π_x(c) δ_e` for a suitable point `x`) gives `dim_k V_n(S) <= |B_Z(mn)| = 2mn + 1`.
5. **Contradiction.** Take `n = 2m + 2`. Then `n^2 = (2m + 2) n > 2mn + 1`, which contradicts steps
   3 and 4.

So no such `ψ` exists. In particular the target holds for every infinite minimal Cantor system.

## What this settles and what it does not

- **The title's residual case.** The target's title allows "entirely degenerate" embeddings to
  survive. None do. The point-column bound does not look at leading coefficients, so the split into
  degenerate and spectrally complete elements is not needed.
- **The `s = 1` case of the commutative-rank conjecture** (`f2-z4-embeds-in-z2-sft-boundary-product-hosts`)
  holds for transformation groupoids of `Z`. The same argument gives rank `<= s` for every
  `LC(X, k) ⋊ Z^s`, and GK dimension `<= D` for any acting group of growth degree `D`.
- **What it does not reach.** The Cuntz groupoid of `L(1, 2)` has a `Z`-valued cocycle with AF kernel,
  but its orbits grow exponentially. There the bound `|W_n ∩ 𝒢_η|` is exponential in `n` and gives
  nothing, so the `s = 1` conjecture for `L(1, 2)` stays open. By
  `leavitt-commuting-units-are-algebraically-dependent` its NO side is at least as hard as the open
  question whether `L_2 ⊗ L_2` embeds unitally in `L_2`.
