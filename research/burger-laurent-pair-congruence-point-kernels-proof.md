---
rg: 2
id: burger-laurent-pair-congruence-point-kernels-proof
kind: route
title: "Bounded displacement bounds the base orbits; interval windows push the kernel map to Følner or small-boundary sets; a non-torsion character has an abelian stabilizer, so infinite kernel orbits would make EL_2 amenable, and finite ones are congruence"
target: burger-laurent-pair-wobbling-point-kernels-are-congruence
requires: [wobbling-normal-relative-t-subgroups-have-bounded-displacement, elementary-linear-semidir-pair-relative-t, elementary-sl2-laurent-integers-is-finitely-generated]
---

Notation as in the target. The action of `e ∈ E` on `M` is written `v ↦ e(v)`. In `Γ_p`,
`(e, m) k (e, m)^{-1} = e(k)` for `k ∈ M`, since `M` is abelian.

## Step 1: bounded kernels (item 1)

`R` is a finitely generated ring (by `t, t^{-1}`), so `(Γ_p, M)` has relative property (T) by
`elementary-linear-semidir-pair-relative-t`. `M` is normal in `Γ_p`. The image of `Γ_p` in
`W(Z)` is an isomorphic copy, so `wobbling-normal-relative-t-subgroups-have-bounded-displacement`
applies with `Γ = Γ_p` and `H = M`. It gives `B` with `|Mx| ≤ 2B − 1` for all `x`. By orbit-stabilizer,
`[M : K_x] = |Mx|`.

## Step 2: equivariance (item 2)

For `g = (e, m)`: `Stab_M(gx) = g Stab_M(x) g^{-1} = e(K_x)`. So `ρ: Y → Q_x`, `y ↦ K_y`, is
`Γ_p`-equivariant for the action of `Γ_p` on subgroups of `M` through `Γ_p → E`. It is onto
`Q_x` because `Y = Γ_p x`.

## Step 3: the window lemma

*Let `Y = Γ_p x` and `ρ` as in Step 2. Let `J ⊂ Z` be a finite interval and
`A_J = ρ(Y ∩ J)`. Then for every `g ∈ Γ_p`, `|g A_J \ A_J| ≤ 2 d(g)`.*

Proof. Let `q ∈ gA_J \ A_J`. Then `q = g ρ(y) = ρ(gy)` for some `y ∈ Y ∩ J`. If `gy ∈ J` then
`q ∈ A_J`, which is excluded. So `gy ∉ J`, while `|gy − y| ≤ d(g)`. Hence `gy` lies among the
`d(g)` integers just left of `J` or the `d(g)` integers just right of `J`. Since `q = ρ(gy)`, at most
`2d(g)` values of `q` occur. ∎

Fix `x` and enumerate intervals `J_0 = {x} ⊂ J_1 ⊂ J_2 ⊂ …`, each obtained from the previous one
by adding one integer, alternately on the right and the left, so that `⋃ J_n = Z`. Put
`A_n = A_{J_n}`. Then:
- `A_0 = {K_x}`, `A_n ⊆ A_{n+1}`, and `|A_{n+1}| ≤ |A_n| + 1`;
- `⋃_n A_n = ρ(Y) = Q_x`;
- `|g A_n \ A_n| ≤ 2 d(g)` for every `g` and `n`.

**Consequences.**
- (a) If `Q_x` is finite, then `A_n = Q_x` for large `n`, so every size `1 ≤ k ≤ |Q_x|` is attained
  by some `A_n`. This proves item 5: the edge boundary of `A_n` in the Schreier graph for `S` is
  at most `Σ_{s∈S} |sA_n \ A_n| ≤ 2 D_S`. Taking `|A_n| = ⌊|Q_x|/2⌋` bounds the Cheeger constant
  by `2D_S/⌊|Q_x|/2⌋`.
- (b) If `Q_x` is infinite, then `|A_n| → ∞`. Since `|gA_n| = |A_n|`, we get
  `|gA_n Δ A_n|/|A_n| ≤ 4 d(g)/|A_n| → 0` for every `g ∈ Γ_p`. Every `e ∈ E` is the image of
  `(e, 0) ∈ Γ_p`. So `(A_n)` is a Følner sequence for the transitive `E`-set `Q_x`, and a weak-*
  limit of the uniform probabilities on `A_n` is an `E`-invariant mean on `Q_x ≅ E/Stab_E(K_x)`.
  That is, `Stab_E(K_x)` is co-amenable in `E`.

## Step 4: `E` is not amenable

Suppose `E` is amenable. Then `Γ_p` is amenable, as an extension of the amenable group `E` by the
abelian group `M`. So the left regular representation `λ` of `Γ_p` on `ℓ²(Γ_p)` has almost invariant
vectors. By relative (T) (Step 1), `λ` has a nonzero `M`-invariant vector `f`. Then `f` is constant on
each coset `gM`, which is infinite, so `f` is not square-summable unless it is `0`. Contradiction.
So `E` is not amenable.

## Step 5: an amenable co-amenable subgroup forces amenability

*If `L ≤ G` is amenable and `G/L` carries a `G`-invariant mean, then `G` is amenable.*

Proof. Let `n` be a left-invariant mean on `ℓ^∞(L)` and `μ` a `G`-invariant mean on `ℓ^∞(G/L)`.
For `f ∈ ℓ^∞(G)`, put `F(g) = n(l ↦ f(gl))`. For `l' ∈ L`,
`F(gl') = n(l ↦ f(gl'l)) = F(g)` by left invariance of `n`. So `F` is a bounded function on `G/L`,
and we put `ν(f) = μ(F)`. Then `ν` is a mean on `G`. For `γ ∈ G` and `(γf)(g) = f(γ^{-1}g)`,
we have `F_{γf}(g) = F_f(γ^{-1}g)`, so `ν(γf) = μ(γF_f) = μ(F_f) = ν(f)`. ∎

## Step 6: characters and their stabilizers

- *Characters.* `M` is an `F_p`-vector space, so its characters take values in the `p`-th roots of
  unity. Fix `ζ = e^{2πi/p}`. Then `M̂ = (R^*)²`, where `R^* = Hom_{F_p}(R, F_p)`, and
  `(α, β)` is the character `(v_1, v_2) ↦ ζ^{α(v_1) + β(v_2)}`.
- *Module structure.* `R^*` is an `R`-module by `(rα)(s) = α(rs)`. `E` acts on `M̂` by
  `(eχ)(v) = χ(e^{-1}(v))`. For `e = [[a, b], [c, d]]`,
  `χ ∘ e = (aα + cβ, bα + dβ)`, which is the row vector `(α, β)` times the matrix `e`. So
  `e ∈ Stab_E(χ)` iff `χ ∘ e = χ` iff `(α, β)(e − 1) = 0` in `(R^*)²`.
- *Torsion.* Let `T ⊂ R^*` be the `R`-torsion submodule, `{α : fα = 0 for some f ≠ 0}`. It is a
  submodule because `R` is a domain. `R^*/T` is torsion-free, so it embeds in the vector space
  `V = F ⊗_R (R^*/T)` over `F = F_p(t)`. Call `χ = (α, β)` *torsion* if `fχ = (fα, fβ) = 0` for
  some `f ≠ 0`, that is, if `α, β ∈ T`.

**Claim 6.1.** *If `χ` is not torsion, then `Stab_E(χ)` is abelian.*

Proof. Let `ᾱ, β̄ ∈ V` be the images of `α, β`. They are not both `0`. For `e ∈ Stab_E(χ)`, the
relation `(α, β)(e − 1) = 0` maps to `(ᾱ, β̄)(e − 1) = 0` in `V²`, with `e ∈ SL_2(R) ⊂ SL_2(F)`.
- If `ᾱ, β̄` are `F`-linearly independent, then the entries of
  `(ᾱ, β̄)(e − 1) = ((a−1)ᾱ + cβ̄, bᾱ + (d−1)β̄)` vanish only if `a = d = 1` and `b = c = 0`. So
  `Stab_E(χ) = 1`.
- Otherwise `ᾱ = xw` and `β̄ = yw` with `0 ≠ w ∈ V` and `0 ≠ (x, y) ∈ F²`. The relation becomes
  `((x, y)(e − 1)) w = 0`, so `(x, y) e = (x, y)`. Choose `g ∈ GL_2(F)` with `(x, y) = (1, 0)g`.
  Then `geg^{-1}` fixes `(1, 0)`, so its first row is `(1, 0)`, and `det = 1` forces
  `geg^{-1} = [[1, 0], [c', 1]]`. These matrices form a group isomorphic to `(F, +)`, so
  `Stab_E(χ)` is abelian. ∎

**Claim 6.2.** *Let `K ≤ M` have finite index and `W = K^⊥ = {χ ∈ M̂ : χ|_K = 1}`. If every `χ ∈ W`
is torsion, then the `E`-orbit of `K` is finite. Otherwise `Stab_E(K)` is virtually abelian.*

Proof.
- `W` is finite of order `[M:K]`, and `K = W^⊥` by duality for the finite group `M/K`. Since the
  `E`-actions on `M` and on `M̂` are compatible, `e(K) = K` iff `e(W) = W`. So
  `Stab_E(K) = Stab_E(W)`.
- If every `χ ∈ W` is torsion, let `f` be the product of annihilators of the finitely many
  elements of `W`. Then `f ≠ 0` and `fW = 0`, so every `χ ∈ W` is trivial on `fM`, that is,
  `fM ⊆ W^⊥ = K`. Let `e ∈ E(fR)`. Then `e(v) − v ∈ fM ⊆ K` for all `v ∈ M`, so `e(K) = K`.
  `E(fR)` is the kernel of `E → SL_2(R/fR)`, a finite group, since `R/fR` is finite. So
  `Stab_E(K)` has finite index, and the orbit is finite.
- Otherwise pick a non-torsion `χ ∈ W`. `Stab_E(W)` permutes the finite set `W`. The kernel `N` of
  this permutation action has finite index in `Stab_E(W)` and lies in `Stab_E(χ)`, which is abelian
  by Claim 6.1. So `Stab_E(K)` is virtually abelian. ∎

## Step 7: every kernel orbit is finite and congruence (item 3)

Fix `x`. By Step 1, `K_x` has finite index.
- *Finiteness.* Suppose `Q_x` is infinite. By Claim 6.2, applied to `K = K_x`, `Stab_E(K_x)` is
  virtually abelian, hence amenable. By Step 3(b) it is co-amenable in `E`. By Step 5, `E` is
  amenable, contradicting Step 4. So `Q_x` is finite.
- *The level ideal.* Put `K_0 = ⋂_{K ∈ Q_x} K`. It is a finite intersection of subgroups of finite
  index, so it has finite index. It is `E`-invariant, since `Q_x` is an `E`-orbit. Let
  `I_x = {r ∈ R : (r, 0) ∈ K_0}`, an additive subgroup.
  - For `r ∈ I_x` and `b ∈ R`: `e_21(b)(r, 0) = (r, br) ∈ K_0`, so `(0, br) = (r, br) − (r, 0) ∈ K_0`.
  - Then `e_12(1)(0, br) = (br, br) ∈ K_0`, so `(br, 0) = (br, br) − (0, br) ∈ K_0`, and `br ∈ I_x`.
    So `I_x` is an ideal.
  - Taking `b = 1` in the first bullet gives `(0, r) ∈ K_0` for `r ∈ I_x`. So `I_x M = I_x ⊕ I_x ⊆ K_0`.
  - `r ↦ (r, 0)` induces an injection `R/I_x ↪ M/K_0`, so `|R/I_x| ≤ [M : K_0] < ∞`. `R` is
    infinite, so `I_x ≠ 0`.
- *Congruence action.* For `e ∈ E(I_x)` and `K ∈ Q_x`: `e(v) − v ∈ I_x M ⊆ K` for all `v`, so
  `e(K) = K`. So `E(I_x)` acts trivially on `Q_x`. It is normal in `E` with finite quotient, and
  the transitive `E`-set `Q_x` is a quotient of `E/E(I_x)`.

## Step 8: unbounded levels (item 4)

- Let `J ≠ 0` be an ideal. `JM ≠ 0` acts nontrivially on `Z` by faithfulness, so some `x` has
  `JM ⊄ K_x`.
- Suppose `|Q_x| ≤ N` for all `x`. Then `[M : K_0(x)] ≤ (2B−1)^N`, and so `|R/I_x| ≤ (2B−1)^N`.
- `R` is a principal ideal domain. Each nonzero ideal is `gR` with `g ∈ F_p[t]` monic and
  `g(0) ≠ 0`, and `|R/gR| = p^{deg g}`. So only finitely many nonzero ideals have index at most
  `(2B−1)^N`.
- Their product `J` is nonzero and lies in every `I_x`, so `JM ⊆ I_x M ⊆ K_x` for all `x`. This
  contradicts the first bullet. So `sup_x |Q_x| = ∞`.

## Step 9: items 5 and the `[[X]]` case

Item 5 is Step 3(a), which applies because every `Q_x` is finite by Step 7. `E` is finitely
generated: `E_2(Z[t,t^{-1}])` is generated by five matrices by
`elementary-sl2-laurent-integers-is-finitely-generated`, and reduction mod `p` maps elementary
matrices onto elementary matrices. So the Cheeger statement can be applied to a finite generating
set of `E`, lifted to `Γ_p` as `(e, 0)`. For `Γ_p ≤ [[X]]`, compose with the embedding
`[[X]] ≤ W(Z)` of Step 6 of `wobbling-normal-relative-t-locally-finite-proof`.
