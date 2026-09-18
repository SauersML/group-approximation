---
rg: 2
id: aleph-one-eg-is-equivalent-to-relative-countable-eg-proof
kind: route
title: Combine the landed direction REG_omega implies EG up to aleph_1 with the per-pair amalgam criterion, whose aleph_1-fold amalgam has cd 2 under the pd hypothesis
target: aleph-one-eg-is-equivalent-to-relative-countable-eg
requires:
  - relative-countable-eg-gives-eg-for-aleph-one-groups
  - relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two
  - continuous-free-chain-unions-have-gd-two
---

## (i) ⇒ (ii)

This is `relative-countable-eg-gives-eg-for-aleph-one-groups`.

## (ii) ⇒ (iii)

Let `(H,G)` be a countable pair with `cd G ≤ 2` and `pd I_{G/H} ≤ 1`. By the cd bound in `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two`, `cd Γ_{ℵ_1}(H,G) ≤ 2`, and `|Γ_{ℵ_1}(H,G)| ≤ ℵ_1`.

- If `cd Γ_{ℵ_1}(H,G) = 2`, then (ii) gives `gd ≤ 2`.
- If `cd ≤ 1`, the group is free by Stallings–Swan, so `gd ≤ 1`.

## (iii) ⇒ (i)

Let `(H,G)` be a countable pair as in REG_ω, and let `K` be a 2-dimensional `K(H,1)`.

1. By (iii), `gd Γ_{ℵ_1}(H,G) ≤ 2`, which is condition (c) of `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two`.
2. (c) ⇒ (a) ⇒ (b) there gives a 2-dimensional `K(G,1)` containing `K` as a subcomplex, inducing `H ≤ G`.

So REG_ω holds. ∎

## Biography items

- **Item 1.** Suppose (ii) fails. Then (iii) fails, so some `Γ_{ℵ_1}(H,G)` with `cd ≤ 2` has `gd ≥ 3`. It cannot have `cd ≤ 1`, by Stallings–Swan.
- **Item 3.** This is the failure of (a) in the engine, since (a) ⇔ (c) there.
- **Item 2.** Suppose `H` is a vertex group of a free-edge splitting of `G` whose other vertex groups have `gd ≤ 2`. Then Lemma 2 of `continuous-free-chain-unions-have-gd-two-proof` gives (b) for the pair, hence (d): `gd Γ_{ℵ_1} ≤ 2`. That is a contradiction.
- **Almost gd 2.** For `ω ≤ δ < ω_1`, `Γ_δ = ⁎_H {G_ξ : ξ < δ} ≅ Γ_{ℵ_0}(H,G)` is countable with `cd ≤ 2`, so countable EG gives it `gd ≤ 2`. `Γ_{ℵ_1}` is the continuous union of these.

## Consistency checks

- **Free `H`, and `H = 1`.** For `H = 1` the engine gives `gd G ≤ 2 ⇔ gd ⁎^{ω_1} G ≤ 2`, and REG_ω for `H = 1` is countable EG. For free `H`, REG_ω holds for the pair by the free-base lemma, and (iii) holds for the pair by (b) ⇒ (d). Neither contradicts anything.
- **Direction check on the pd hypothesis.** The pd hypothesis is used only to know that `Γ_{ℵ_1}` is a cd-2 group. Without it, the engine's Klein-bottle calibration gives `cd Γ_2 = 3`, so (iii) would not be a statement about cd-2 groups. This matches the necessity of the pd condition recorded in `relative-countable-eg-gives-eg-for-aleph-one-groups`.
