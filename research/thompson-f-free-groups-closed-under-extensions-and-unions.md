---
rg: 2
id: thompson-f-free-groups-closed-under-extensions-and-unions
kind: claim
title: Groups containing no copy of Thompson's group F are closed under subgroups, extensions and directed unions, so every ascending HNN extension of a residually finite group omits F
distinct_from:
  extensions-with-f-free-outer-kernel-contain-thompson-f: that lifts a copy of F from a quotient G/K into G when Out(K) is F-free; this is the converse direction, that a copy of F in G forces one in N or in G/N, with no hypothesis.
  thompson-f-is-not-residually-finite: that puts residually finite groups in the class; this closes the class under extensions and unions, which reaches groups that are not residually finite.
---

**ESTABLISHED** (lane proof below, elementary; the two facts about `F` are classical and cited). No priority is
claimed. The closure is folklore-level, but no printed statement was found.

## Statement

Let `𝒳` be the class of groups with no subgroup isomorphic to Thompson's group `F`.
1. `𝒳` is closed under subgroups.
2. **Extensions.** If `N ⊴ G`, `N ∈ 𝒳` and `G/N ∈ 𝒳`, then `G ∈ 𝒳`. More precisely, if `F ≤ G` then `F`
   embeds in `N` or in `G/N`.
3. **Directed unions.** A directed union of groups in `𝒳` is in `𝒳`.
4. Every residually finite group is in `𝒳`.

So `𝒳` contains the closure of the residually finite groups under subgroups, extensions and directed unions. That
closure includes every elementary amenable group and every locally residually finite group. In particular:

5. **Ascending HNN extensions.** If `B ∈ 𝒳` and `σ : B → B` is injective, then `B*_σ ∈ 𝒳`. So every ascending
   HNN extension of a residually finite group, for example of any group acting faithfully on a locally finite
   rooted tree, contains no copy of `F`.

## Proof

Two facts about `F` from Cannon–Floyd–Parry, Enseign. Math. 42 (1996), §4:
- (CFP1) every nontrivial normal subgroup of `F` contains `F' = [F, F]`, that is, every proper quotient of `F` is
  abelian;
- (CFP2) `F'` is the set of elements of `F` that are the identity near `0` and near `1`, and for dyadic
  `0 < a < b < 1` the elements supported in `[a, b]` form a subgroup isomorphic to `F`.

So `F'` contains a copy `F_0` of `F`, the elements supported in `[1/4, 3/4]`.

1. Clear.
2. Let `F ≤ G`. Then `F ∩ N ⊴ F`.
   - If `F ∩ N = 1`, then `F` embeds in `G/N`.
   - Otherwise `F ∩ N ⊇ F'` by (CFP1), so `F_0 ≤ F' ≤ N` and `F` embeds in `N`.
3. `F` is finitely generated. So a copy of `F` in a directed union lies in one member.
4. This is `thompson-f-is-not-residually-finite`: `F` is not residually finite, and residual finiteness passes to
   subgroups.
5. `B*_σ = N ⋊ ⟨t⟩`, where `N = ⋃_(n ≥ 0) t^n B t^(−n)` is a directed union of copies of `B`. So `N ∈ 𝒳` by 3,
   `Z ∈ 𝒳`, and `B*_σ ∈ 𝒳` by 2. ∎

**Calibration.** `F` is itself an ascending HNN extension of a copy of `F` along an infinite-index endomorphism.
This is consistent with 5, because that base contains `F`. Closure under amalgams and non-ascending HNN
extensions is not claimed.

## Lesson for general BH

Thompson's `F` cannot be created by extensions or unions. In any construction by extensions, directed unions and
ascending HNN extensions, `F` must already be present in one of the pieces. So any group assembled from residually finite pieces by
extensions and ascending HNN extensions, which covers every branch-group L-presentation extension (Grigorchuk,
Basilica), is `F`-free, whatever the answer to the amenability of `F`. For the questions near Boone–Higman that
ask for infinite-dimensional finiteness without `F` (Kourovka 21.140, Zaremsky 2.8, FFKLZ Q2.4), this moves the
whole difficulty onto finiteness properties.
