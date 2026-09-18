---
rg: 2
id: relative-eg-pair-base-meets-its-conjugates-in-free-groups-proof
kind: route
title: Restriction H^2(G,-) -> H^2(H,-) is onto under the pd hypothesis; on a module coinduced from H the Mackey decomposition splits off the identity double coset, forcing H^2 of every H cap gHg^{-1} to vanish
target: relative-eg-pair-base-meets-its-conjugates-in-free-groups
requires:
  - relative-countable-eg-gives-eg-for-aleph-one-groups
---

All modules are left modules. Cohomology commutes with arbitrary products of coefficient modules.

## Step 0: restriction is onto

From `0 → I_{G/H} → Z[G/H] → Z → 0` the long exact `Ext_{ZG}(−,M)` sequence contains
`H^2(G,M) −res→ H^2(H,M) → Ext^2_{ZG}(I_{G/H},M)`,
using Shapiro's lemma `Ext^n_{ZG}(Z[G/H],M) ≅ H^n(H,M)`, under which the map from `Ext^n(Z,M)` is restriction. The last term is `0` since `pd I_{G/H} ≤ 1`. So `res^G_H: H^2(G,M) → H^2(H,M)` is onto for **every** `ZG`-module `M`.

## Step 1: Mackey decomposition of a coinduced module

Let `N` be a `ZH`-module and `M = Coind_H^G N = Hom_{ZH}(ZG, N)`, with `(γ f)(x) = f(xγ)`.

- **Shapiro.** `H^n(G,M) ≅ H^n(H,N)` is the composite of `res^G_H` with `ε_*`, where `ε: M → N`, `f ↦ f(1)`, is an `H`-map.
- **Splitting.** As an `(H,H)`-bimodule, `ZG = ⊕_{D ∈ H\G/H} Z[D]`. Hence `Res_H M = ∏_D M_D` with `M_D = Hom_{ZH}(Z[D], N)`, each an `H`-submodule (the right action of `H` preserves `D`). For `D = H`, `M_H = Hom_{ZH}(ZH,N) ≅ N` and the projection `M → M_H ≅ N` is `ε`.
- **The factor `M_D`, `D = HgH`.** An `f ∈ M_D` is determined by `F(h) = f(gh)` for `h ∈ H`. The `H`-linearity of `f` says exactly `F(lh) = (glg^{-1}) · F(h)` for `l ∈ L' := H ∩ g^{-1}Hg`, and the `H`-action is `(k·F)(h) = F(hk)`. So `M_D ≅ Coind_{L'}^H N^{(g)}`, where `N^{(g)}` is `N` with `l ∈ L'` acting as `glg^{-1}`. By Shapiro, `H^2(H, M_D) ≅ H^2(L', N^{(g)})`.

## Step 2: (A)

Fix `g ∈ G ∖ H`, so `D = HgH ≠ H`. By Step 1,
`H^2(G,M) −res→ ∏_{D'} H^2(H, M_{D'})`,
and the `D' = H` component of this map is the Shapiro isomorphism `H^2(G,M) ≅ H^2(H,N)`.

By Step 0 the map is onto. Take the target element that is `0` in the `H`-component and arbitrary `y` in the `D`-component. A preimage `x` has Shapiro image `0`, so `x = 0` and `y = 0`. Hence

`H^2(L', N^{(g)}) = 0` for every `ZH`-module `N`. (∗)

Now let `W` be any `ZL'`-module. Put `L = gL'g^{-1} = H ∩ gHg^{-1} ≤ H`, let `W'` be `W` with `l ∈ L` acting as `g^{-1}lg`, and set `N = Coind_L^H W'`.

- By Mackey for `Res_L Coind_L^H` (the same computation as Step 1 with `(L,H)` in place of `(H,G)`), `Res_L N` has `W'` as a product factor (the identity double coset), hence as a direct summand. So `H^2(L, W')` is a direct summand of `H^2(L, Res_L N)`.
- Conjugation by `g` identifies `(L', N^{(g)})` with `(L, Res_L N)` and `(L',W)` with `(L,W')`. By (∗), `H^2(L, Res_L N) = 0`, hence `H^2(L', W) = 0`.

So `H^2(L',−) ≡ 0`. By dimension shifting (embed `W` in `Coind_1^{L'} W`, which is cohomologically trivial) `H^n(L',−) ≡ 0` for all `n ≥ 2`, so `cd L' ≤ 1`. Thus `H ∩ gHg^{-1} ≅ L'` has `cd ≤ 1` and is free by Stallings–Swan (Swan 1969, valid for all groups). ∎

## Step 3: (B)

Take `M = Q/Z` with trivial action. `Q/Z` is an injective abelian group, so the universal coefficient theorem gives `H^2(−;Q/Z) ≅ Hom(H_2(−;Z), Q/Z)` naturally. By Step 0, `Hom(H_2 G, Q/Z) → Hom(H_2 H, Q/Z)` is onto. `Hom(−,Q/Z)` is exact and faithful, so `H_2(H) → H_2(G)` is injective. ∎

## Corollaries

Assume `H` is not free.

1. **Conjugation into `H`.** If `U ≤ H` is non-free and `gUg^{-1} ≤ H` with `g ∉ H`, then `gUg^{-1} ≤ H ∩ gHg^{-1}`, which is free by (A); subgroups of free groups are free, contradiction. Taking `U = H` and `g ∈ N_G(U)` or `C_G(U)` gives the normalizer and centralizer statements.
   - **Commensurator.** Assume `H` is torsion-free of finite `cd` (automatic in the relative Eilenberg--Ganea setting, where `cd G ≤ 2`). If `g ∈ Comm_G(H) ∖ H`, then `H ∩ gHg^{-1}` has finite index in `H`, so by Serre's theorem it has `cd = cd H ≥ 2` and is not free, contradicting (A). So `Comm_G(H) = H`.
2. **Normal `H ≠ G`.** Take `g ∉ H`; `H ∩ gHg^{-1} = H` is not free. Instances:
   - `H_L = ker(A_L → Z)` (all generators to `1`) in the right-angled Artin group of a connected triangle-free graph `L` containing a cycle. Here `cd A_L = 2`, and by Bestvina–Brady `H_L` is finitely generated but not finitely presented (`L` is connected, not simply connected), hence not free. E.g. `L` a square gives the Stallings–Bieri kernel in `F_2 × F_2`.
   - fibres of mapping tori; `Z^2 ⊴ K` (Klein bottle group).
3. **Finite index.** `Comm_G(H) = G`, so Corollary 1 forces `H = G`.
4. **`BS(1,n) = Z[1/n] ⋊ Z`, `n ≠ 0`.** Let `A = Z[1/n]` be the normal abelian subgroup and `H` non-free, so `H` is not cyclic.
   - If `H ∩ A = 1`, `H` embeds in `G/A ≅ Z`, contradiction.
   - If `H ≤ A`: if `H ≠ A`, any `g ∈ A ∖ H` normalizes `H` (`A` is abelian); if `H = A`, then `t ∉ H` normalizes `H`. Either way Corollary 1 kills it.
   - Otherwise pick `0 ≠ x = p/n^j ∈ H ∩ A` and `h ∈ H` mapping to `k ≠ 0` in `Z`. Conjugation by `h` acts on `A` by multiplication by `n^{±k}`, so `H ∩ A ⊇ x · Z[1/n^k] = pZ[1/n]`, which has index `≤ |p|` in `A`; and `HA/A = kZ`. So `[G:H] < ∞`, and Corollary 3 gives `H = G`.
   Hence every admissible pair in `BS(1,n)` has free base or `H = G`.
5. **HNN and amalgams.** In `⟨B,t | tα(c)t^{-1} = β(c)⟩`, `β(C) = tα(C)t^{-1} ≤ B ∩ tBt^{-1}`, and `t ∉ B`. In `A *_C B`, for `b ∈ B ∖ C` one has `b ∉ A` and `C ∩ bCb^{-1} ≤ A ∩ bAb^{-1}`.
6. **Calibration against a failing pair with free intersections.** `G = F(b,c) × ⟨a⟩`, `u = [b,c]`, `H = ⟨u⟩ × ⟨a⟩`.
   - For `g = (w, a^m) ∉ H`, i.e. `w ∉ ⟨u⟩`: `H ∩ gHg^{-1} = (⟨u⟩ ∩ w⟨u⟩w^{-1}) × ⟨a⟩ = ⟨a⟩`, because the cyclic subgroup generated by a non-proper-power in a free group is malnormal. So (A) holds.
   - `H_2(H) ≅ Z` is generated by `u ⊗ a`, which maps to `[u] ⊗ a ∈ H_1(F_2) ⊗ H_1(Z) ⊆ H_2(G)` (Künneth), and `[u] = 0` in `H_1(F_2)`. So (B) fails, and `pd I_{G/H} ≥ 2`.
   So (A) alone does not characterize admissible pairs.

## Calibration

- `H` free: (A) is vacuous-true. `H = G`: vacuous.
- `G = Z^2 ⊇ H = ⟨x⟩`: `I_{G/H} ≅ Z[G/H]` has `pd = cd H = 1`, and `H ∩ gHg^{-1} = H ≅ Z` is free, as (A) requires.
- Klein bottle `Z^2 ⊴ K`: the pd condition is known to fail (`relative-countable-eg-gives-eg-for-aleph-one-groups`), and (A) detects it at once since `H ∩ gHg^{-1} = Z^2`.
