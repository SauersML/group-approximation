---
rg: 2
id: cantor-crossed-hochschild-bound-via-fox-and-idempotent-telescope
kind: route
title: Resolve LC(X) by diagonal idempotents, resolve the crossed product by B ⊗_A B tensored with a kP-resolution of k, and add up
target: cantor-crossed-hosts-of-finite-cd-have-bounded-polynomial-rank
requires: [polynomial-rank-is-at-most-hochschild-dimension]
---

## Part 1: `hd(LC(X, k)) <= 1`

Put `A = LC(X, k)`, so `A^e = A ⊗ A = LC(X × X, k)`.
- Choose clopen partitions `π_0 = {X}, π_1, π_2, ...`, each refining the last, that
  separate points. This is possible because `X` is compact metrizable and totally
  disconnected.
- Let `e_j = Σ_(U ∈ π_j) 1_U ⊗ 1_U`, the indicator of `∪_U U × U`. These are
  idempotents with `e_(j+1) e_j = e_(j+1)`, and `∩_j supp e_j` is the diagonal.
- `A = A^e / I`, where `I` is the ideal of functions vanishing on the diagonal. A
  locally constant function vanishing on the diagonal vanishes on a clopen
  neighbourhood of it. By compactness that neighbourhood contains some `supp e_j`.
- So `I = ∪_j A^e(1 - e_j) = ⊕_(j>=0) A^e(e_j - e_(j+1))`, a direct sum of
  summands of `A^e`. It is projective, and `pd_(A^e) A <= 1`.

## Part 2: `hd(A ⋊ P) <= hd(A) + cd_k(P)`

Let `B = A ⋊ P`, the skew group ring. `B = ⊕_g A g = ⊕_g g A` is free over `A` on both
sides. Put `M = B ⊗_A B`.
- **Right `kP`-action.** Set `(x ⊗ y)·h = x h ⊗ h^(-1) y`. It is well defined over
  `⊗_A` because `h^(-1) A h = A`. It is a right action, and it commutes with the
  `B`-bimodule structure.
- **Freeness.** `Φ: B ⊗_k kP -> M`, `x ⊗ h ↦ x h ⊗ h^(-1)`, is bijective, with inverse
  `y ⊗ g ↦ y g ⊗ g^(-1)` on the left-`B` basis `{1 ⊗ g}` of `M`. It satisfies
  `Φ(x ⊗ h h') = Φ(x ⊗ h)·h'`. So `M` is a free right `kP`-module.
- **Coinvariants.** `M ⊗_(kP) k = B ⊗_A B / (x h ⊗ y - x ⊗ h y) = B ⊗_B B = B`,
  via multiplication.
- **Resolution.** Let `F_• -> k` be a projective resolution of length `c`. `M` is
  `kP`-flat, so `M ⊗_(kP) F_• -> B` is an exact complex of `B`-bimodules of length
  `c`. Its terms are direct summands of direct sums of copies of `M`.
- **Each term.** Take a projective `A^e`-resolution `Q_• -> A` of length `hd(A)`.
  The functor `B ⊗_A - ⊗_A B` is exact, because `B` is flat over `A` on both sides. It
  sends `A ⊗ A` to `B ⊗_k B`. So `pd_(B^e) M <= hd(A)`.
- **Dimension shifting** then gives `pd_(B^e) B <= hd(A) + c`.

For `P = F_m`, the Fox resolution `0 -> kF_m^m -> kF_m -> k -> 0` gives `c = 1`. For
`P = Z^2`, the Koszul resolution gives `c = 2`. In both cases `c = cd_k(P)`.

## Part 3: `hd(A ⊗ C) <= hd A + hd C`

Tensor a projective `A^e`-resolution of `A` with a projective `C^e`-resolution of `C`
over `k`. By Künneth over a field the result is exact, and it resolves `A ⊗ C`. Its
terms are projective over `A^e ⊗ C^e = (A ⊗ C)^e`.

## Part 4: the hosts

- `B_Ω = (LC(Ω) ⋊ Z) ⋊ Z`, or directly `LC(Ω) ⋊ Z^2`, has `hd <= 1 + 2 = 3`.
- `L_∂ = LC(∂F_d) ⋊ F_d` has `hd <= 1 + 1 = 2`. No Leavitt-path presentation is used.
- By Part 3, `hd(B_Ω ⊗ L_∂) <= 5`.
- By `polynomial-rank-is-at-most-hochschild-dimension`, the polynomial rank of
  `B_Ω ⊗ L_∂` is at most `5`.
- `F_2[Z^6] ⊇ F_2[N^6] = F_2[x_1..x_6]`. So there is no embedding, unital or not, and
  `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` fails at `G = Z^6`.

Part 5 of the claim is Parts 1, 2 and the polynomial-rank bound together. `k[Z wr Z]`
contains `k[Z^m]` for every `m`.

**What this does not reach.** The Z^4 test `f2-z4-embeds-in-z2-sft-boundary-product-hosts`
needs rank 4, and the bound here is 5. So the test stays open unless
`hd(B_Ω ⊗ L_∂) <= 3` can be proved. For instance, it would suffice to show both
`hd(B_Ω) <= 2` and that `L_∂` is quasi-free as a Leavitt path algebra.
