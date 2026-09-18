---
rg: 2
id: rover-nekrashevych-vdr-sigma-full-for-every-r
kind: claim
title: For every self-similar G and every r, the characters of V_{d,r}(G) are the sum-invariant characters of G, and all Sigma-invariants are full whenever V_{d,r}(G) has type F_m
distinct_from:
  rover-nekrashevych-bnsr-invariants-are-full: that is the case r = 1, where type-one partitions form a directed poset; this is every r, including gcd(r, d-1) > 1, where type-r partitions are not directed and the poset is nonpure.
  rover-nekrashevych-characters-are-sum-invariant: that identifies Hom(V_d G, R) for r = 1; item 1 here is the same identification for V_{d,r} G with every r >= 1.
  rover-nekrashevych-polynomial-activity-tower-sigma-full: that proves full Sigma-invariants for contracting polynomial-activity G through the activity tower; this needs no hypothesis on G beyond type F_m of the whole group.
---

**ESTABLISHED (proof in `rover-nekrashevych-vdr-sigma-full-via-type-r-partitions`; unreviewed).**

Let `d >= 2`, `k = d − 1`, `X = {0, ..., d − 1}`, `r >= 1` and `C_r = {0, ..., r − 1} × X^ω`. Let `G <= Aut(X^*)`
be self-similar, with no other hypothesis: it need not be contracting, finitely generated, or of bounded activity.

- The cones are `C_α = α X^ω` for `α in {0, ..., r − 1} × X^*`. A cone is *proper* if it is not all of `C_r`.
- `Γ = V_{d,r}(G)` is the group of homeomorphisms `h` of `C_r` that have a *table*: cone partitions
  `C_r = ⊔_i C_{α_i} = ⊔_i C_{β_i}` and `g_i in G` with `h(α_i w) = β_i g_i(w)`.
- For `g in G` and a cone `C_α`, `g_(α) in Γ` acts by `α w ↦ α g(w)` on `C_α` and as the identity elsewhere.
- `χ in Hom(G, R)` is *sum-invariant* if `χ(g) = Σ_{x in X} χ(g|_x)` for all `g`.

1. **Characters.** Fix a proper cone `C_α`. The map `Φ ↦ (g ↦ Φ(g_(α)))` is a linear isomorphism from `Hom(Γ, R)`
   onto the space of sum-invariant characters of `G`, and it does not depend on `α`.
   - The inverse sends `χ` to `Φ_χ(h) = Σ_i χ(g_i)`, for any table of `h`.
   - Every real character of `Γ` vanishes on the Higman–Thompson group `V_{d,r}`.
   - If `Φ != 0`, then `Φ|_{Γ_A} != 0` for every nonempty clopen `A ⊆ C_r`. Here `Γ_A` is the subgroup of elements
     that are the identity off `A`.
2. **Σ-invariants.** If `Γ` has type `F_m` for some `m >= 1`, then `Σ^m(Γ) = S(Γ)`.

**Consequences.**

- For every self-similar `G`, `d` and `r`, computing `Σ^*(V_{d,r}G)` reduces entirely to two questions:
  - the finiteness type of `V_{d,r}G`;
  - the sum-invariant characters of `G`, which `sum-invariant-characters-of-contracting-groups-via-nucleus` computes
    for contracting `G`.
- For `d = 2`, or for `r ≡ 1 mod k`, the type-`r` partitions are directed, and the proof reduces to that of
  `rover-nekrashevych-bnsr-full-via-type-one-partitions`. The new case is `gcd(r, k) > 1`, where directedness fails:
  - Take `d = 3` and `r = 2`, with `P = {C_0 ∪ C_{10}, C_{11} ∪ C_{12}}` and `Q = {C_0 ∪ C_{11}, C_{10} ∪ C_{12}}`.
  - Both are partitions of `C_2` into blocks of two cones.
  - The pairwise intersections are single cones, which have odd type. So no partition into even-type blocks refines
    both `P` and `Q`.
- For `r ≡ 1 mod k`, `V_{d,r}G ≅ V_d G` by a prefix-replacement conjugation, so item 1 recovers
  `rover-nekrashevych-characters-are-sum-invariant` item 2.

## Attempts

- 2026-09-18 (w6-101): proved via the action on the poset of partitions of `C_r` into clopen blocks of type `r` with at
  least `m + 1` blocks.
  - Contractibility cannot use directedness. It uses instead a directed union of finite truncated `r mod k` partition
    posets, which `r-mod-k-partition-posets-truncations-highly-connected` shows are highly connected.
  - Ascending links are `1 mod k/gcd(r, k)` rank selections.
  - Stabilizers are virtually `Γ^n`.
  - Item 1 supplies the missing living-character input for Meinert's criterion.
