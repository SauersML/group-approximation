---
rg: 2
id: compact-extension-kazhdan-fixed-algebras-blind-proof
kind: route
title: Mackey ranges of a compressed subgroup are conjugate and nested, and a compact group admits no proper self-compression
target: compact-extension-kazhdan-fixed-algebras-are-blind
requires: []
---

# Proof

Setting as in the claim. Write `Γ' = gΓg^(-1) <= Γ`.

**Step 1, the right K-action.** Let `r_k(x,h) = (x, hk)`. It preserves `μ × Haar` and commutes with `G`:
`g r_k (x,h) = (gx, α(g,x)hk) = r_k g(x,h)`. So `r_K` preserves `B_Λ` for every `Λ <= G`. The action of `K`
on `L²(Y)` is continuous.

**Step 2, K acts ergodically on B_Γ and B_Γ'.** Let `f ∈ B_Γ` be `r_K`-invariant. Then `f(x,h) = f_0(x)`
a.e. by Fubini, and `f_0` is Γ-invariant, hence constant. The same holds for `Γ'`, because `Γ' ≅ Γ` acts on
`X` by `x ↦ gγg^(-1)x`, which is conjugate by `g` to the Γ-action. So `Γ'` acts ergodically.

**Step 3, point realization.** `B_Γ` is a separable abelian von Neumann algebra with a faithful normal trace
and a continuous trace-preserving `K`-action. By Mackey's point realization it is `L^∞(W,ν)` for a Borel
`K`-space `W`, and by Step 2 `K ↷ W` is ergodic. An ergodic p.m.p. action of a compact second countable
group is essentially transitive (standard; e.g. Zimmer, *Ergodic Theory and Semisimple Groups*,
Chapter 2). So `B_Γ ≅ L^∞(K/L)` `K`-equivariantly for a closed `L <= K`, with Haar measure on `K/L`.
Likewise `B_Γ' ≅ L^∞(K/L')`.

**Step 4, two equivariant maps.**
(a) `Γ' <= Γ` gives `B_Γ ⊆ B_Γ'`. This is a `K`-equivariant measure-algebra embedding. It is realized by
a `K`-equivariant measurable factor map `p : K/L' → K/L`.
(b) `f ↦ f ∘ g^(-1)` maps `B_Γ` onto `B_Γ'`: if `f` is Γ-invariant, then `f∘g^(-1)(gγg^(-1)y) = f(γ g^(-1)y) = f∘g^(-1)(y)`,
and `g^(-1)` gives the inverse map. It preserves the measure and commutes with `r_K` (Step 1). So it is a
`K`-equivariant isomorphism `q : K/L → K/L'` (a.e.).

A measurable `K`-equivariant map between transitive `K`-spaces agrees a.e. with a `K`-map (standard;
Zimmer, op. cit., Appendix B). A `K`-map `K/A → K/B` has the form
`xA ↦ xcB` with `A <= cBc^(-1)`. So:

- from (a), `L' <= cLc^(-1)` for some `c ∈ K`;
- from (b), `q` is bijective a.e. with equivariant inverse, so `L = dL'd^(-1)` for some `d ∈ K`.

Hence `L <= (dc)L(dc)^(-1)`, i.e. `zLz^(-1) <= L` with `z = (dc)^(-1)`.

**Step 5, compact compression lemma.** If `K` is compact, `L <= K` closed and `zLz^(-1) <= L`, then
`zLz^(-1) = L`.

*Proof.* The closure of `{z^n : n >= 1}` is a compact semigroup in a compact group, hence a group, so it
contains `e`. Choose `n_i -> ∞` with `z^(n_i) -> e`. For `n >= 1`, iterating the hypothesis gives
`z^n L z^(-n) <= zLz^(-1)`. Fix `ℓ ∈ L`. Then `z^(n_i) ℓ z^(-n_i) ∈ zLz^(-1)`, which is closed, and it
converges to `ℓ`. So `L <= zLz^(-1)`. ∎

**Step 6, conclusion.** We have `L' = d^(-1)Ld <= cLc^(-1)`. Step 5 applied to `z = (dc)^(-1)` gives
`L' = cLc^(-1)`. Then
`p : xL' ↦ xcL` is a bijection `K/L' → K/L`, so it is an isomorphism of measure spaces. The embedding
`B_Γ ⊆ B_Γ'` is therefore onto: `B_Γ = B_Γ'`. With Step 4(b), `g·B_Γ = B_Γ' = B_Γ`.

**Homogeneous extensions.** `Y_M = X ×_α K/M` is the factor of `Y` given by the `G`-invariant subalgebra
`A_M = L^∞(Y)^(r_M) ⊆ L^∞(Y)` (the `r_M`-invariant functions). Then `L^∞(Y_M)^Λ = B_Λ ∩ A_M`. Both are
preserved by `g`, so `g·(B_Γ ∩ A_M) = B_Γ ∩ A_M`. With `K = S_k`, `M` a point stabilizer and
`α` any `S_k`-valued cocycle, `Y_M` is the finite extension `X ×_α {1,...,k}`.

**Finite extensions lift soficity (for the Consequence).** Let `Θ : L^∞(X) ⋊ G → Π_𝒰 M_n` be a sofic
embedding, with `Θ(L^∞(X)) ⊆ D_𝒰`, `Θ(u_g)` permutations, and `Θ` trace-preserving. For the finite
extension, `L^∞(X ×_α [k]) ⋊ G` embeds in `M_k(L^∞(X) ⋊ G)` by `f ⊗ e_i ↦ f e_ii` and
`u_g ↦ U_g = Σ_π (1_(A_(g,π)) ⊗ P_π) u_g`, where `A_(g,π) = {x : α(g, g^(-1)x) = π}` and `P_π` is the
permutation matrix of `π`. This `U_g` is the Koopman unitary of the extension, since `u_g f u_g^* = f∘g^(-1)`. Lift the partition `{A_(g,π)}_π` to exact partitions
of `{1,...,n}` in each model. Then `Σ_π Θ(1_(A_(g,π))) ⊗ P_π · Θ(u_g)` is a permutation matrix on
`{1,...,n} × {1,...,k}`. `D_𝒰 ⊗ D_k` is the diagonal of `M_k(Π_𝒰 M_n) = Π_𝒰 M_(kn)`. The normalized trace
restricts correctly. So the extension is sofic. Conversely `X` is a factor of the extension, and
factors of sofic actions are sofic. ∎

**Scope note.** Step 3 needs `Γ` to act ergodically on the base `X`, not merely on `Y`. For a tower of two
compact extensions, the middle level is not Γ-ergodic, so the claim is not asserted for distal towers of
height >= 2.
