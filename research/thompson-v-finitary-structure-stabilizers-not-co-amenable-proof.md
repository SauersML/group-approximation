---
rg: 2
id: thompson-v-finitary-structure-stabilizers-not-co-amenable-proof
kind: route
title: Average uniform measures on quasi-equivariant breakpoint sets into an invariant mean on a Cantor orbit, after pushing the small-defect part off by disjoint translates
target: thompson-v-finitary-structure-stabilizers-are-not-co-amenable
requires:
  - thompson-v-amenable-actions-are-free-off-fixed-points
---

Notation as in the target. For a finite nonempty set `X`, `u_X` is the uniform probability on `X`, and `‖·‖` is
the `ℓ¹` norm. Means act on bounded functions by integration, and invariance reads `m(f∘g) = m(f)`.

## Step 1. Uniform measures on nearby finite sets

Let `X, Y` be finite and nonempty with `|X Δ Y| <= c` and `|Y| = b > c`. Then `‖u_X − u_Y‖ <= 3c/(b − c)`.

*Proof.* Let `a = |X|` and `n = |X ∩ Y|`. Then `|a − b| <= c`, `a − n <= c`, `b − n <= c`, and
`a, b >= b − c`. So
`‖u_X − u_Y‖ = n|1/a − 1/b| + (a − n)/a + (b − n)/b <= c/max(a,b) + c/a + c/b <= 3c/(b − c)`. `∎`

## Step 2. Theorem A

Suppose `m({ω : |D(ω)| <= N}) = 0` for every `N`. For `ω` with `D(ω) ≠ ∅` put `μ_ω = u_(D(ω))`, a probability on
`Q`, and put `μ_ω = δ_(q_0)` otherwise, for a fixed `q_0 ∈ Q`. Define `ν(U) = m(ω ↦ μ_ω(U))` for `U ⊆ Q`. This is a
mean on `Q`.

Fix `g` and `U`. By invariance of `m` applied to `f(ω) = μ_ω(U)`, `ν(U) = m(ω ↦ μ_(gω)(U))`. Also
`ν(g^(-1)U) = m(ω ↦ (g_*μ_ω)(U))`. Hence
`|ν(g^(-1)U) − ν(U)| <= m(ω ↦ ‖g_*μ_ω − μ_(gω)‖)`.

`g_*μ_ω = u_(gD(ω))` and `μ_(gω) = u_(D(gω))`, and `|gD(ω)| = |D(ω)|`. When `|D(ω)| > N > c_g`, Step 1 with
`c = c_g` bounds the integrand by `3c_g/(N − c_g)`. On the null set `|D(ω)| <= N` it is at most `2`. So
`|ν(g^(-1)U) − ν(U)| <= 3c_g/(N − c_g)` for every `N`. Hence `ν` is invariant, contradicting the hypothesis on
`Q`. `∎`

## Step 3. Theorem B, item 1

Let `Ω = Vσ` and `D(ω) = Δ(ω, σ)`, finite since `ω = gσ`. Write `ℓ(ω) = |D(ω)|`.

**(a) Quasi-equivariance.** By the triangle inclusion and equivariance,
`D(gω) = Δ(gω,σ) ⊆ Δ(gω,gσ) ∪ Δ(gσ,σ) = gD(ω) ∪ D(gσ)`. Applying this to `g^(-1)` and `gω` gives
`D(ω) ⊆ g^(-1)D(gω) ∪ D(g^(-1)σ)`, so `gD(ω) ⊆ D(gω) ∪ gD(g^(-1)σ)`. Hence
`|D(gω) Δ gD(ω)| <= ℓ(gσ) + ℓ(g^(-1)σ) =: c_g`.

**(b) Symmetry of defect.** `D(g^(-1)σ) = Δ(g^(-1)σ,σ) = g^(-1)Δ(σ,gσ) = g^(-1)D(gσ)`, so
`ℓ(g^(-1)σ) = ℓ(gσ)`.

**(c) Reverse triangle.** For `x ∈ V` and `ω ∈ Ω`,
`D(xσ) = Δ(xσ,σ) ⊆ Δ(xσ,xω) ∪ Δ(xω,σ) = xD(ω) ∪ D(xω)`, so `ℓ(xω) >= ℓ(xσ) − ℓ(ω)`.

**(d) Small defect is null.** Let `m` be an invariant mean on `Ω`, fix `N`, and put `B = {ω : ℓ(ω) <= N}`.
Choose `g_1, g_2, ...` inductively with `ℓ(g_(k+1)σ) > 2N + max_(i<=k) ℓ(g_i^(-1)σ)`. This is possible because
`ℓ` is unbounded on `Ω`. Let `i < j` and suppose `g_iω ∈ B` and `g_jω ∈ B`. By (c) with `x = g_j` and
`ω' = g_i^(-1)σ`, `ℓ(g_jg_i^(-1)σ) >= ℓ(g_jσ) − ℓ(g_i^(-1)σ) > 2N`. By (c) again,
`ℓ(g_jω) = ℓ((g_jg_i^(-1))(g_iω)) >= ℓ(g_jg_i^(-1)σ) − ℓ(g_iω) > 2N − N = N`, which is a contradiction. So the sets
`g_i^(-1)B` are pairwise disjoint. Each has `m`-measure `m(B)`, so `K·m(B) <= 1` for every `K`, and `m(B) = 0`.

By (a), (d) and Theorem A, `Ω` has no invariant mean. `Ω ≅ V/Stab(σ)`. Co-amenability passes to overgroups,
and `V/(gHg^(-1)) ≅ V/H` as `V`-sets. So every subgroup of a conjugate of `Stab(σ)` is not co-amenable. For a
finitely generated group, no invariant mean on `V/H` is equivalent to `φ_S(V/H) > 0`. `∎`

## Step 4. Theorem B, item 2

Let `Ω_1 = {x ∈ Ω : Stab(x) ≤ Stab(gσ) for some g}`. Since `Stab(hx) = h Stab(x) h^(-1)` and
`h Stab(gσ) h^(-1) = Stab(hgσ)`, this set is `V`-invariant. Suppose `m(Ω_1) > 0`. The normalized restriction of `m`
is an invariant mean on `Ω_1`. In each orbit of `Ω_1` choose `x_0`, and choose `σ_0 ∈ Vσ` with
`Stab(x_0) ≤ Stab(σ_0)`. The map `hx_0 ↦ hσ_0` is well defined and equivariant `Ω_1 -> Vσ`. The pushforward of the
mean is an invariant mean on `Vσ`, which contradicts item 1. `∎`

## Step 5. The examples of `Q` in the target

- **A countable `V`-invariant `Q ⊆ C`.** An invariant mean `ν` on `Q` gives a `V`-invariant finitely additive
  probability `U ↦ ν(U ∩ Q)` on clopen sets. The element with `[0] -> [00]`, `[10] -> [01]`, `[11] -> [1]` gives
  `ν[00] = ν[0]` and `ν[01] = ν[10]`, so `ν[10] = 0`. `V` is transitive on nonempty proper clopen sets: match
  both sets and both complements by equal numbers of cones, which is possible since a cone splits into two. So
  every proper cone is null and `ν(C) = ν[0] + ν[1] = 0`, a contradiction. This is the halving of
  `thompson-v-amenable-actions-are-free-off-fixed-points`, item 4.
- **`Q = V/K` with `K` not co-amenable.** There is no invariant mean by definition.

## Step 6. The corollary for `T`

Let `Q = {w0^∞} ∪ {w1^∞}` over finite words `w`. Every element of `V` replaces prefixes, so `V` preserves `Q`.
`σ` is as in the target, `Σ` is the set of maps `Q -> Q` with `g·τ = gτg^(-1)`, and `Δ(τ,τ')` is the set where
`τ` and `τ'` differ. `Δ` is symmetric, satisfies the triangle inclusion, and is equivariant.

**Finitary.** Let `g ∈ V` map cones `u_1, ..., u_n` (a dyadic partition) to cones `v_1, ..., v_n` by prefix
replacement. A pair `{uw01^∞, uw10^∞}` inside one `u_i` goes to the pair `{v_iw01^∞, v_iw10^∞}`, which is a
`σ`-pair. So `gσg^(-1)` differs from `σ` only at the images of the `2n` endpoints `u_i0^∞`, `u_i1^∞`, which is a
finite set.

**`T ≤ Stab(σ)`.** For `t ∈ T` the `u_i` are consecutive in the cyclic order, and the `v_i` are consecutive in the
same cyclic order. The endpoint pairs `{u_i1^∞, u_(i+1)0^∞}` (indices mod `n`, with `{1^∞, 0^∞}` for the wrap)
go to the endpoint pairs `{v_i1^∞, v_(i+1)0^∞}`, which are `σ`-pairs. Interior pairs are preserved as above.

**Equality (not needed for the corollary).** If `h ∈ V` commutes with `σ`, then `h` preserves the closed
equivalence relation `E = diag ∪ graph(σ)`, so `h` induces a homeomorphism of `C/E = S^1`. On each cone of its
domain partition this homeomorphism is an increasing dyadic affine map of arcs, so it is an orientation-preserving
dyadic PL homeomorphism, that is, an element `t ∈ T`. Then `h` and `t` agree off `Q`, where `C -> S^1` is
injective. `Q` is dense and both maps are continuous, so `h = t`.

**Unbounded defect.** For odd `n >= 3` take the standard partition `0, 10, ..., 1^(n-2)0, 1^(n-1)` into
consecutive cones `u_1, ..., u_n`, and let `g` send `u_i` to `u_(2i mod n)`. For every `i`, `gσg^(-1)` pairs
`u_(2i)1^∞` with `u_(2i+2)0^∞`, while `σ` pairs `u_(2i)1^∞` with `u_(2i+1)0^∞`. So `|Δ(gσ,σ)| >= n`.

Theorem B applies. `F ≤ T` gives the statement for `F`. `∎`

## Calibration

- **`H = V`, and any `σ` with bounded defect.** Step 3(d) is where unboundedness is used. There is no conclusion,
  as there must not be.
- **Point stabilizers.** For `Σ = P(Q)`, `σ = {q}` and `Δ = Δ`, the defect is bounded by 2 and Theorem B is
  silent. Those stabilizers are already null by item 4 of the required claim. Nothing false is reproduced.
- **Theorem A with `Q` meanless is essential.** For amenable `G` every `G`-set has an invariant mean, so the
  hypothesis on `Q` is never met there. The contradiction always passes through Step 5.
