---
rg: 2
id: rn-lamplighter-is-a-function-field-stein-group-proof
kind: route
title: Pieces lambda_w g lambda_v^{-1} are exactly the R-affine ball maps because R meets F_2[[pi]] in F_2[t,1/t]; decorating Stein-Farley leaves by cells of T_0 x T_infinity keeps contractibility by a Quillen retraction and makes stabilisers finite
target: rn-lamplighter-is-a-function-field-stein-group
requires: []
---

Notation is that of the claim.
- `λ_x(y) = x + πy` for `x ∈ {0,1}`, and `λ_w = λ_{x_1} ∘ ... ∘ λ_{x_k}` for a word `w = x_1...x_k`.
- `λ_w` is a bijection of `O` onto the ball `B_w = a_w + π^k O`, where `a_w = x_1 + x_2π + ... + x_kπ^{k-1}`.
- Every ball in `O` is some `B_w`.
- `V_2(G)` is the group of homeomorphisms `h` of `O` for which there are words `v_1, ..., v_n` and `w_1, ..., w_n`
  such that the balls `B_{v_i}` partition `O`, the balls `B_{w_i}` partition `O`, and `h = λ_{w_i} g_i λ_{v_i}^{-1}`
  on `B_{v_i}` for some `g_i ∈ G`.

## 1. Realisation

**Lemma 1.1.** `R ∩ O = F_2[t, t^{-1}]` inside `K_π`.

*Proof.* `F_2[t, t^{-1}]` is a principal ideal domain, and `R` is its localisation at the prime `π`. An element
`r/π^j` of `R` with `r ∈ F_2[t^{±1}]` and `π ∤ r` lies in `O` exactly when `j ≤ 0`. ∎

**Lemma 1.2.** Every element of `V_2(G)` lies in `PAff(O; R)`.

*Proof.* Take `g(y) = t^m y + p` with `p ∈ F_2[t^{±1}]`, a ball `B_v = a_v + π^{k}O` and a ball
`B_w = a_w + π^{l}O`, where `a_v, a_w ∈ F_2[π] ⊂ R`. Then
`λ_w g λ_v^{-1}(x) = t^m π^{l-k} x + (a_w + π^l p - t^m π^{l-k} a_v)`.
The multiplier lies in `R^×` and the translation lies in `R`. ∎

**Lemma 1.3.** Every element of `PAff(O; R)` lies in `V_2(G)`.

*Proof.* Let `h(x) = ux + b` on a ball `B_v = a_v + π^kO` of the defining partition. Refine the partition so that
each piece `B_v` is mapped into a ball.
- An affine map sends balls to balls, so `h(B_v)` is a ball `B_w = a_w + π^lO`.
- The map `g = λ_w^{-1} h λ_v` is a bijection `O → O` of the form `y ↦ u' y + b'` with
  `u' = u π^{k-l} ∈ R^×` and `b' ∈ R`.
- Since `g` maps `O` onto `O`, we get `|u'|_π = 1`, and `b' = g(0) ∈ O`.
- Now `R^× = t^Z × π^Z`, because `F_2^× = 1`. Hence `u' = t^m`.
- By Lemma 1.1, `b' ∈ F_2[t^{±1}]`.
- So `g ∈ G` and `h = λ_w g λ_v^{-1}` on `B_v`. ∎

Lemmas 1.2 and 1.3 give (1). For the germ-groupoid description, take a homeomorphism of `O` that agrees near each point with
some element of `Aff(R)`. By compactness it agrees with finitely many such elements on the pieces of a clopen
partition, and that partition refines to a partition into balls. So the topological full group is exactly
`PAff(O; R)`.

For general `q` and `a`, run the same argument with `π = t - a`, `λ_x` for `x ∈ F_q`, and
`R = F_q[t, t^{-1}, π^{-1}]`. The multipliers that occur are `t^Z π^Z` (times `F_q^*` for `AGL_1`). Lemma 1.1 holds
verbatim.

## 2. Heights and `G`-orbits on `X = T_0 × T_∞`

**Invariance.** `Aff(K_v)` fixes the end `∞` of `T_v`.
- The map `x ↦ ux + b` shifts `β_v` by `-log_2 |u|_v`, since translations preserve radii.
- For `u ∈ R^×`, `|u|_v = 1` at every place `v ∉ S`.
- The product formula `Π_v |u|_v = 1` therefore gives `Σ_{v∈S} log|u|_v = 0`. So `ℋ = β_π + β_0 + β_∞` is
  `Aff(R)`-invariant.
- For `G` alone, `|t|_0 |t|_∞ = 1`, so `β = β_0 + β_∞` is `G`-invariant.
- `λ_x^{-1}(y) = π^{-1}(y - x)`, with `|π^{-1}|_0 = 1` and `|π^{-1}|_∞ = 1/2`. So `λ_x^{-1}` raises `β` by exactly `1`.
  This is the splitting rule in (3).

**Orbit count.** A vertex of `X` is a pair of balls `(B_0, B_∞)`. Use `t^Z` to put `B_0 = a + F_2[[t]]`. At level
`h`, this forces `B_∞ = b + t^{-h}F_2[[t^{-1}]]`. The normalisation is unique, since `t` shifts `β_0` freely.
- The remaining group is the translations by `F_2[t^{±1}]`, acting on
  `K_0/F_2[[t]] × K_∞/t^{-h}F_2[[t^{-1}]]`.
- **Kernel.** The kernel of `F_2[t^{±1}] → K_0/F_2[[t]] × K_∞/t^{-h}F_2[[t^{-1}]]` is spanned by the monomials
  `t^j` with `0 ≤ j ≤ -h`. It has order `2^{max(0, 1-h)}`, and it is the stabiliser.
- **Cokernel.** The kernel and cokernel are `H^0` and `H^1` of `O(D)` on `P^1_{F_2}`, for a divisor `D` of degree
  `-h` supported on `{0, ∞}` (the adelic description of line-bundle cohomology). So the kernel has dimension
  `max(0, 1-h)` and the cokernel has dimension `max(0, h-1)`. Direct check for `h = 2`: the cokernel is spanned by
  the class of `(t^{-1}, 0)`.
- Hence level `h` carries `2^{max(0,h-1)}` orbits with stabilisers of order `2^{max(0,1-h)}`. This is (2).
- At `h = 1`, both the kernel and the cokernel are trivial, so `G` acts simply transitively. The level set, with
  adjacency "up one step in one tree and down one step in the other", is `DL(2,2)`, the Diestel–Leader graph, which
  is the standard Cayley graph of `Z/2 ≀ Z`.

## 3. The decorated Stein–Farley complex

**Background.** `𝒱(n)` is the set of homeomorphisms `g: ⊔_n O → O` that are piecewise `λ_w γ λ_v^{-1}`, with
`γ ∈ G`. An *expansion* `Φ: ⊔_m O → ⊔_n O` is a finite forest of simple splittings, and on each copy it is some
`λ_w`. The group `G^n ⋊ S_n` acts on `⊔_n O` on the right.

The Stein–Farley poset `P` is defined as follows.
- Elements are the classes `[g] = g(G^n ⋊ S_n)`.
- The order is `[g] ≤ [gΦγ]`, for any expansion `Φ` and any `γ`.
- It is well defined, since `γ λ_x = λ_{γ(x)} γ|_x`.
- `|P|` is contractible, since `P` is directed.

**Leafwise-affine transport.** Every map that occurs here is *leafwise affine*: copy `j` of the source goes into
copy `i` of the target by the restriction of one affine map `a_j ∈ Aff(K)`. This holds for expansions, for `G^n ⋊ S_n`
and for their composites.
- For `λ_x` and for `G` it is clear.
- The section `γ|_x = λ_{γ(x)}^{-1} γ λ_x` is again affine on `K`: an affine function of `y` that agrees with `γ|_x`
  on `O` agrees with it on `K`.

For such `Ψ` and `ρ ∈ C(X)^n` (tuples of cells of `X`), put `(Ψ_*ρ)_j = a_j^{-1} ρ_i`. Here `Aff(K)` acts on `X`
through `Aff(K_0) × Aff(K_∞)` by cellular automorphisms. This transport is functorial, `(ΨΨ')_* = Ψ'_* Ψ_*`, and it
preserves the face order.

**The poset `𝒬`.**
- Elements are the classes `[g, ρ]` with `g ∈ 𝒱(n)`, `ρ ∈ C(X)^n`, and `(g, ρ) ~ (gγ, γ_*ρ)`.
- The order is: `[g, ρ] ≤ [h, τ]` if there are representatives with `h = gΦ` for an expansion `Φ` and
  `Φ_*ρ ≤ τ` in the face order.
- By functoriality this is well defined and transitive.
- `G` acts faithfully on `O`, so `gγ = g` forces `γ = 1`. With the leaf count, this gives antisymmetry.
- For fixed `g`, the elements `[g, ρ]` have unique representatives with that `g`. So the fibre over `[g]` is the cell
  poset of `X^n`, whose realisation is the barycentric subdivision of `X^n`, which is contractible.

**Contractibility.** Let `p: 𝒬 → P`, `[g, ρ] ↦ [g]`.
- *Fibre.* Fix `[g]`. The preimage `p^{-1}(P_{≤[g]})` consists of the elements `[h, ρ]` with `g = hΦ`, where `g` is
  chosen within its class.
- *The retraction.* Put `r[h, ρ] = [g, Φ_*ρ]`.
  - **Well defined.** Suppose `hδΦ' = hΦε`. Then `δΦ' = Φε`, so `Φ'_* δ_* = ε_* Φ_*`, and
    `[g, ε Φ'_* δ_*ρ] = [g, Φ_*ρ]`.
  - **Monotone.** It is monotone by functoriality.
  - **Identity on the fibre.** It restricts to the identity on the fibre `{[g, σ]}`.
  - **Above the identity.** It satisfies `r ≥ id`.
- *Conclusion.* So `p^{-1}(P_{≤[g]})` deformation retracts onto the fibre, and it is contractible. By Quillen's
  fibre lemma, `|𝒬| ≃ |P|`, which is contractible.

**Action and stabilisers.** `V_2(G)` acts by `v[g, ρ] = [vg, ρ]`.
- `v` fixes `[g, ρ]` exactly when `v = gγg^{-1}` with `γ ∈ G^n ⋊ S_n` and `γ_*ρ = ρ`.
- `G` is discrete in `Aff(K_0) × Aff(K_∞)`, because `F_2[t^{±1}]` is discrete in `K_0 × K_∞` and `t^Z` is discrete.
  So its cell stabilisers in `X` are finite, and `Stab(ρ)` is finite.
- `V_2(G)` is transitive on `𝒱(n)`. So the orbits of `n`-leaf elements are the `(G^n ⋊ S_n)`-orbits on `C(X)^n`.
- Each leaf carries the `G`-invariant height `β(ρ_i)`. By §2, an expansion raises it by `1` per splitting.

This proves (3). With `B = λ_w(O)` and `q = λ_w ρ`, the leaf of `(λ_w, ρ)` becomes the pair `(B, q)`, a point of
`Y`, and `ℋ(B, q) = β(ρ)`.

## 4. What is left for `F_n`

By Brown's criterion, (3) reduces `F_n` to one statement. Take the Morse function `f = Σ_i φ(β(ρ_i))`, with
`φ(h) = c^{|h-1|}` and `c > 2`.
- **Cocompact sublevel sets.** Sublevel sets of `f` are cocompact: they bound the number of leaves and the heights,
  and each level has finitely many `G`-orbits by §2.
- **The requirement.** Descending links of vertices with `f` large must be `(n-1)`-connected.

The two ends behave differently.

- **High leaves (`h > 1`).** Descending moves are merges, the moves down one step in `T_0` or `T_∞` (unique), and
  splits. A split is descending when `2φ(h+1) < φ(h)`, which fails for `h ≥ 1`.
- **Low leaves (`h < 1`).** Descending moves are splits, since `2c^{-h} < c^{1-h}`, and the up moves (two in each
  tree). The single-leaf part is `{split} * S^0 * S^0`, which is a cone.
- **Open part.** What is not done is the join with the merge part, and the treatment of cells of `X`, not only
  vertices, in the order complex. This is the open step (4) of the claim.
