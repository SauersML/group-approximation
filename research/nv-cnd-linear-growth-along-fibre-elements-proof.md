---
rg: 2
id: nv-cnd-linear-growth-along-fibre-elements-proof
kind: route
title: "The imaginary part of an almost invariant vector state is a paradoxical measure; spectral shells of the centre turn this into linear growth"
target: nv-cnd-functions-grow-at-most-linearly-along-fibre-elements
requires:
  - cantor-maps-by-v-embed-in-next-brin-thompson-group
---

Only item 3 of the target uses the prerequisite. Items 1, 2 and 4 are proved from
scratch below. Standard imports (textbook, cited by chapter, not verbatim): the GNS
correspondence `ψ(g) = ‖b(g)‖²` for a cocycle `b` of a unitary representation `π`, with
`b(gh) = b(g) + π(g)b(h)` (Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Ch. 2 and
App. C), and the spectral theorem for one unitary operator.

## 0. Notation

`C`, `A = C(C,Z)`, `G = A ⋊ V`, `z = 1_C` as in the target. In `G`,
`h (M·1_U) h^{-1} = M·1_{hU}` for every `h ∈ V` and clopen `U` (set image; no
canonicity is needed), and `M·1_{U⊔W} = (M·1_U)(M·1_W)`, the two factors commuting.

`G` is perfect (artifact `research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md`,
§3(b), reproduced): `V` is simple, so `V ≤ [G,G]`; `[h,f] = h·f − f`, so
`1_{[u]} − 1_{[u']} ∈ [G,G]` for proper cylinders; and
`(1_{[00]} − 1_{[1]}) + (1_{[01]} − 1_{[1]}) − (1_{[0]} − 1_{[1]}) = −1_{[1]}`.
Every proper `1_{[w]}` is `V`-conjugate to `1_{[1]}`, and the `1_{[w]}` span `A`.

## 1. Two exact error identities

Let `π` be unitary on `H`, `ξ` a unit vector, `M` fixed, `T_U = π(M·1_U)`,
`s(U) = Im⟨T_U ξ, ξ⟩`.

**(A) Additivity.** For disjoint `U, W`, `T_{U⊔W} = T_U T_W`, and
`⟨T_UT_Wξ,ξ⟩ − ⟨T_Uξ,ξ⟩ − ⟨T_Wξ,ξ⟩ + 1 = ⟨(T_W − 1)ξ, (T_U^* − 1)ξ⟩`.
Taking imaginary parts, and using `‖(T^* − 1)ξ‖ = ‖(T − 1)ξ‖` for unitary `T`,
`|s(U⊔W) − s(U) − s(W)| ≤ ‖(T_U − 1)ξ‖ ‖(T_W − 1)ξ‖`.

**(B) Invariance.** For `h ∈ V`, `T_{hU} = π(h)T_Uπ(h)^*`. Put `η = π(h)^*ξ`,
`δ = η − ξ`, so `‖δ‖ = ‖π(h)ξ − ξ‖`. Then
`⟨T_{hU}ξ,ξ⟩ − ⟨T_Uξ,ξ⟩ = ⟨T_Uη,η⟩ − ⟨T_Uξ,ξ⟩ = ⟨T_Uδ,ξ⟩ + ⟨T_Uξ,δ⟩ + ⟨T_Uδ,δ⟩`
`= (⟨δ,ξ⟩ + ⟨ξ,δ⟩) + ⟨δ,(T_U^* − 1)ξ⟩ + ⟨(T_U − 1)ξ,δ⟩ + ⟨T_Uδ,δ⟩`.
The bracket is real. Hence
`|s(hU) − s(U)| ≤ 2‖δ‖ ‖(T_U − 1)ξ‖ + ‖δ‖²`.

Also `‖(T_{hU} − 1)ξ‖ = ‖(T_U − 1)η‖ ≤ ‖(T_U − 1)ξ‖ + 2‖δ‖`.

## 2. The paradox inequality (target item 1)

Keep §1's notation. Put `a = ‖(T_{[0]} − 1)ξ‖`, `d = max_i ‖π(h_i)ξ − ξ‖`, `t = s([0])`.

By (B) with `h = h_1, h_2, h_3` and `U = [0]`:
`s([1]), s([00]), s([01]) ∈ [t − (2da + d²), t + (2da + d²)]`, and the three operators
`T_{[1]}, T_{[00]}, T_{[01]}` move `ξ` by at most `a + 2d`.

By (A) with `[0] = [00] ⊔ [01]`: `|t − s([00]) − s([01])| ≤ (a + 2d)²`. Hence
`|t − 2t| ≤ 2(2da + d²) + (a + 2d)²`, i.e. `|t| ≤ a² + 8ad + 6d²`.

By (A) with `C = [0] ⊔ [1]`: `|s(C) − t − s([1])| ≤ a(a + 2d)`. Hence
`|s(C)| ≤ 2|t| + (2da + d²) + a(a + 2d) ≤ 3a² + 20ad + 13d² ≤ 14(a + d)² ≤ 28(a² + d²)`.

This is item 1. Only the set identities `h_1[0] = [1]`, `h_2[0] = [00]`, `h_3[0] = [01]`,
`[0] = [00] ⊔ [01]` and `C = [0] ⊔ [1]` were used.

## 3. Linear growth (target item 2)

Let `ψ = ‖b‖²` with `b` a cocycle for `π` on `H`. Write `S = {1_{[0]}, h_1, h_2, h_3}` and
`β(E) = Σ_{s ∈ S} ‖E b(s)‖²` for a projection `E` commuting with `π(G)`. Since `ψ(−g) = ψ(g)`
for cnd functions, take `k ≥ 1`.

**Commutation.** `z` is central, so `b(gz) = b(zg)` gives
`(π(z) − 1) b(g) = (π(g) − 1) b(z)` for all `g ∈ G`. Every spectral projection `E` of
`π(z)` commutes with `π(G)`.

**Invariant part.** Let `P` project onto `ker(π(z) − 1)`. Projecting the commutation identity,
`(π(g) − 1) P b(z) = 0`, so `P b(z)` is `G`-invariant. Let `Q` project onto the
`G`-invariant vectors; `Q` commutes with `π(G)` and `Qπ(g) = Q`, so `Q b` is a homomorphism
`G → H`, hence `0` because `G` is perfect (§0). So `P b(z) = QP b(z) = P Q b(z) = 0`
(`P` and `Q` commute, `Q H ⊆ P H`), and `P b(kz) = Σ_{m<k} π(z)^m P b(z) = 0`.

**Shells.** Write the spectrum of `π(z)` on `(1 − P)H` as `e^{iθ}`, `θ ∈ (−π, π] ∖ {0}`. For
`j ≥ 0` let `B_j = {θ : 2^{-j-1}π < |θ| ≤ 2^{-j}π}` and `E_j = E(B_j)`. The `E_j` are
orthogonal with sum `1 − P`, so `ψ(kz) = Σ_j ‖E_j b(kz)‖²` and `Σ_j β(E_j) ≤ Σ_{s∈S} ψ(s)`.

On `E_j H`, `|e^{iθ} − 1| = 2|sin(θ/2)| ≥ 2|θ|/π > 2^{-j}`, so `π(z) − 1` is invertible
there. Put `v_j = (π(z) − 1)^{-1} E_j b(z)`. The commutation
identity gives `E_j b(g) = (π(g) − 1) v_j` for all `g`, in particular
`E_j b(kz) = (π(z)^k − 1) v_j`.

**Shell `j = 0`.** Here `|e^{iθ} − 1| ≥ √2`, so `‖v_0‖² ≤ ‖E_0 b(z)‖²/2` and
`‖E_0 b(kz)‖² ≤ 4‖v_0‖² ≤ 2ψ(z)`.

**Shells `j ≥ 1`.** For `j ≥ 1`, `B_j ⊆ [−π/2, π/2]`, where `sin θ` has the sign of `θ` and
`|sin θ| ≥ 2|θ|/π > 2^{-j}`. Split `B_j = B_j^+ ⊔ B_j^-` by the sign of `θ`, with projections
`E_± = E(B_j^±)`, `w_± = E_± v_j`; then `E_± b(g) = (π(g) − 1) w_±` and `β(E_+) + β(E_-) = β(E_j)`.
If `w_+ ≠ 0`, apply item 1 (with `M = 1`) to the restriction of `π` to the `G`-invariant
subspace `E_+H` and to `ξ = w_+/‖w_+‖`. The spectral measure of `ξ` for `π(z)` lives on
`B_j^+`, so `Im⟨π(z)ξ,ξ⟩ = ∫ sin θ dμ_ξ > 2^{-j}`. On the right,
`‖π(s)ξ − ξ‖ = ‖E_+ b(s)‖/‖w_+‖` for `s ∈ S`, and `max ≤ Σ`. Item 1 gives
`‖w_+‖² ≤ 28 · 2^j β(E_+)`. The same holds for `w_-` (now `Im⟨π(z)ξ,ξ⟩ < −2^{-j}`). Adding,
`‖v_j‖² ≤ 28 · 2^j β(E_j)`.

Since `|e^{ikθ} − 1| ≤ min(2, k|θ|)` and `|θ| ≤ 2^{-j}π` on `B_j`,
`‖E_j b(kz)‖² ≤ min(4, π²k²4^{-j}) ‖v_j‖² ≤ 28 · min(4, π²k²4^{-j}) 2^j · β(E_j)`.
Using `min(4, y) ≤ 2√y`, `min(4, π²k²4^{-j}) 2^j ≤ 2πk`. So
`‖E_j b(kz)‖² ≤ 56πk β(E_j) ≤ 28π²k β(E_j)`.

**Sum.** `ψ(kz) = ‖E_0 b(kz)‖² + Σ_{j≥1} ‖E_j b(kz)‖² ≤ 2ψ(z) + 28π²k Σ_{s∈S} ψ(s)`, which is
item 2.


## 4. Transfer to nV (target item 3)

Let `n ≥ 2` and `s ∈ (n−1)V`. Write `id × s` for `(x, p) ↦ (x, s(p))` on `C × C^{n−1}`.

If `s` has finite order `r`, then `ψ((id × s)^k)` takes at most `r` values. Otherwise
`k ↦ s^k` is an isomorphism `Z → ⟨s⟩`, and pointwise composition `f ↦ s^f` is a
`V`-equivariant isomorphism `C(C,Z) → C(C,⟨s⟩)`. It extends to an isomorphism
`C(C,Z) ⋊ V → C(C,⟨s⟩) ⋊ V`. By `cantor-maps-by-v-embed-in-next-brin-thompson-group` (with
`Γ = ⟨s⟩ ≤ (n−1)V`), `Φ` embeds the latter in `nV`, and
`Φ(constant map s^k, id)(x, p) = (x, s^k(p))`. So the composite homomorphism
`ρ : G → nV` sends `k·1_C` to `(id × s)^k`. For every cnd `ψ` on `nV`, `ψ ∘ ρ` is cnd on
`G`, and item 2 gives `ψ((id × s)^k) = ψ∘ρ(k·1_C) = O(k)`.

**Other coordinates.** A coordinate permutation `σ` of `C^n` normalizes `nV`, and `ψ ∘ c_σ`
is cnd whenever `ψ` is. So `ψ(g^k) = O(k)` for every `g = σ(id × s)σ^{-1}`, i.e. every `g`
acting as the identity on one coordinate and as an element of `(n−1)V` on the others.

**Commuting products.** `√ψ` is subadditive (`‖b(gh)‖ ≤ ‖b(g)‖ + ‖b(h)‖`). If
`g = g_1 ⋯ g_r` with the `g_i` pairwise commuting and each of the above form, then
`g^k = g_1^k ⋯ g_r^k` and `ψ(g^k) ≤ r Σ_i ψ(g_i^k) = O(k)`. Every
`(g_1, …, g_n) ∈ V^n` equals `(g_1, id, …, id) · (id, g_2, …, g_n)`, a commuting product of
two such elements (the second lies in `id × (n−1)V`, the first is conjugate by a coordinate
permutation to `id × (g_1, id, …)` with `(g_1, id, …) ∈ (n−1)V`, using `n ≥ 2`).

## 5. Positive-drift characters (target item 4)

`Â = Hom(A, T)` is compact metrizable (`A` is countable). `V` acts by
`(hχ)(f) = χ(h^{-1}·f)`, so `(hχ)(1_U) = χ(1_{h^{-1}U})`. Let `ℓ : T → [0,1)` be the Borel
branch with `e^{2πiℓ(w)} = w`. For `χ ∈ Y_+` the measure `τ` is unique: `τ(U) ∈ [0, τ(C)] ⊆ [0, 1/2)`,
so `τ(U) = ℓ(χ(1_U))`. Hence `Y_+` is the set of `χ` with `U ↦ ℓ(χ(1_U))` finitely additive,
`< 1/2`, and `ℓ(χ(1_C)) > 0`: countably many Borel conditions, so `Y_+` is Borel. It is
`V`-invariant, with `τ_{hχ}(U) = τ_χ(h^{-1}U)` and `τ_{hχ}(C) = τ_χ(C)`.

Put `e_χ(U) = τ_χ(U)/τ_χ(C) ∈ [0,1]`, Borel in `χ`, a finitely additive probability measure
in `U`, with `e_{hχ}(U) = e_χ(h^{-1}U)`. For a probability measure `μ` on `Y_+` put
`t(U) = ∫ e_χ(U) dμ(χ)`, again a finitely additive probability measure. With
`‖ν − μ‖_TV = sup_S |ν(S) − μ(S)|` and `δ = max_i ‖(h_i)_*μ − μ‖_TV`:
`t(h_iU) = ∫ e_{h_i^{-1}χ}(U) dμ = ∫ e_χ(U) d((h_i^{-1})_*μ)`, and
`‖(h_i^{-1})_*μ − μ‖_TV = ‖μ − (h_i)_*μ‖_TV` (apply `(h_i)_*`, which preserves `TV`). Since
`0 ≤ e_χ(U) ≤ 1`, `|t(h_iU) − t(U)| ≤ δ`.

With `x = t([0])`: `t([1]), t([00]), t([01]) ≤ x + δ` and `≥ x − δ`. So
`x = t([00]) + t([01]) ≥ 2x − 2δ`, i.e. `x ≤ 2δ`, and `1 = x + t([1]) ≤ 2x + δ ≤ 5δ`.
So `δ ≥ 1/5`. For `Y_-`, apply this to `χ ↦ χ̄`, which commutes with `V`.

**Quantitative corollary.** If `ξ` is a unit vector with `‖π(h_i)ξ − ξ‖ ≤ ε` for `i = 1,2,3`,
and `μ_ξ = ⟨E_A(·)ξ,ξ⟩` is its spectral measure on `Â` for `π|_A`, then
`μ_ξ(Y_+) ≤ 10ε` and `μ_ξ(Y_-) ≤ 10ε`. Indeed `π(h)E_A(S)π(h)^* = E_A(hS)`, so by the
computation in §1(B) (real parts included), `‖(h_i)_*μ_ξ − μ_ξ‖_TV ≤ 2ε`. If `m = μ_ξ(Y_+) > 0`,
the normalized restriction `μ` to the invariant set `Y_+` has `δ ≤ 2ε/m`, so `1/5 ≤ 2ε/m`.
