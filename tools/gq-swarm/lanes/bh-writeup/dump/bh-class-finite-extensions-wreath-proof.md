---
rg: 2
id: bh-class-finite-extensions-wreath-proof
kind: route
title: Kaloujnine--Krasner twice, associativity of permutational wreaths, and induction on composition length
target: bh-class-finite-extensions-reduce-to-finite-simple-wreaths
requires:
  - boone-higman-closed-under-finite-direct-products
---

Classical inputs, not re-read at source for this node:
- **(KK)** Kaloujnine--Krasner: if `N ⊴ G` with `G/N = F` finite, then `G` embeds in
  the regular wreath product `N ≀ F = N^F ⋊ F`. Its embedding of `F` itself, with
  `N = M ⊴ F`, realizes the regular permutation action of `F` inside the
  imprimitive action of `M ≀ (F/M)` on `M x (F/M)` (block coordinates of `F`).
- **(AS)** Associativity: for `B` acting on `X` and `C` acting on `Y`,
  `(A ≀_X B) ≀_Y C ≅ A ≀_{X x Y} (B ≀_Y C)`, with `B ≀_Y C` in its imprimitive
  action on `X x Y`.
- **(MON)** If `A <= A'` and `P <= P'` as permutation groups on `Ω`, then
  `A ≀_Ω P <= A' ≀_Ω P'`.

**Step 1: (FW) ⇒ (FE).** Let `H <= G`, `[G:H] < ∞`, `H <= S_0` with `S_0` finitely
presented simple. Put `N` = normal core of `H` in `G` and `F = G/N`, finite. Then
`N <= S_0`, so `N ∈ 𝓑`.
- By (KK), `G <= N ≀ F` (regular).
- Choose a composition series of `F` with factors `Q_1, ..., Q_r`, taken from a
  maximal normal subgroup downward. By (KK) applied to `M ⊴ F` with `F/M = Q_r`
  simple, and induction on `r`, the regular action of `F` embeds, as a permutation
  group on a set `Ω = Q_1 x ... x Q_r` with `|Ω| = |F|`, in the iterated wreath
  `W_r = (...((Q_1 ≀ Q_2) ≀ Q_3) ...) ≀ Q_r` with regular tops and imprimitive
  action. By (MON), `G <= N ≀_Ω W_r`.
- **Claim.** For every `X ∈ 𝓑` and every such `W_j`, `X ≀_{Ω_j} W_j ∈ 𝓑`. For
  `j = 0` it is `X`. For `j >= 1`, (AS) gives
  `X ≀_{Ω_{j-1} x Q_j} (W_{j-1} ≀ Q_j) ≅ (X ≀_{Ω_{j-1}} W_{j-1}) ≀ Q_j`. By induction
  the inner group lies in some finitely presented simple `S'`, so by (MON) the whole
  group lies in `S' ≀ Q_j`, which is in `𝓑` by (FW).
- Hence `G ∈ 𝓑`.

**Step 2: (FW) ⇒ (SQ).** `U x U` is the base of `U ≀ Z/2`, and `Z/2` is finite simple.

**Step 3: (FE) ∧ (SQ) ⇒ (FW).** Let `S` be finitely presented simple. By (SQ),
`S x S <= U_1` with `U_1` finitely presented simple; then
`S^4 <= U_1 x U_1 <= U_2`, and inductively `S^(2^m) ∈ 𝓑` for all `m`. So
`S^Q ∈ 𝓑` for every finite `Q`. Since `S^Q` has index `|Q|` in `S ≀ Q`, (FE)
gives `S ≀ Q ∈ 𝓑`.

**Step 4: the combined statement.** If `𝓑` is closed under finite direct products
and finite extensions, then (JE) holds (`S x T` contains `S` and `T`), (SQ) holds,
and so (FW) holds by Step 3. Conversely (JE) ∧ (FW) gives (SQ) by Step 2, hence
products by Attempt 10 of `boone-higman-closed-under-finite-direct-products`, and
(FE) by Step 1. ∎
