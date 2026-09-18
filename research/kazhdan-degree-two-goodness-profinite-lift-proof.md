---
rg: 2
id: kazhdan-degree-two-goodness-profinite-lift-proof
kind: route
title: Untwist the lift by Ioana, find a finite orbit of the twisted action on atoms of maximal mass, and conjugate the level homomorphism into a section
target: kazhdan-degree-two-goodness-iff-profinite-measurable-lifts
requires: [ioana-profinite-cocycle-superrigidity, deligne-universal-cover-lattice-is-non-rf-kazhdan]
---

Notation as in the target. `E` is countable, since it is an extension of a countable group by a finite one.
All identities between measurable maps hold for a.e. `x`. `G` is countable, so "for all `g`, a.e. `x`" is the
same as "a.e. `x`, all `g`".

## Step 0. The two reformulations of a lift

- **Skew product.** Given a lift `s`, let `E` act on `X × A` by `e·(x, a) = (π(e)x, s(π(e), x)^{-1} e a)`.
  The second coordinate lies in `A` because `π(s(π(e),x)^{-1} e) = 1`. The cocycle identity for `s` makes this an
  action. It preserves `μ × counting` and covers the `G`-action, and `A` acts by left translation on the fibres,
  which is free. Conversely, given such an action, write `e·(x, 1) = (π(e)x, a_e(x))` and put
  `s(g, x) = ẽ a_ẽ(x)^{-1}` for any lift `ẽ` of `g`. This does not depend on `ẽ` because `A` acts by translation
  on the fibres, and it is a cocycle.
- **Abelian kernel.** Let `A` be abelian, with the `G`-module structure given by conjugation in `E`. Choose a
  set-theoretic section `u : G -> E` with factor set `f(g,h) = u(g)u(h)u(gh)^{-1} ∈ A`, which represents the class
  of `E`. Any `s` with `π s = id` is `s(g,x) = a(g,x) u(g)` with `a : G × X -> A` measurable. Expanding
  `s(gh,x) = s(g,hx) s(h,x)` gives `a(gh,x) = a(g,hx) · g·a(h,x) · f(g,h)`. Give `L^0(X;A)` the action
  `(g·F)(y) = g·F(g^{-1}y)` and put `b(g)(y) = a(g, g^{-1}y)`. Substituting `y = ghx` turns the identity into
  `b(gh) = b(g) · (g·b(h)) · f(g,h)`. In additive notation that is `f = -δb`, with `f` viewed as a constant
  2-cocycle with values in `L^0(X;A)`. Conversely, any measurable 1-cochain `b` with `f = -δb` defines a lift by
  `a(g,x) = b(g)(gx)`. So a lift exists iff the image of the class of `E` in `H^2(G; L^0(X;A))` is zero.

## Step 1. Item 1: a lift forces virtual splitting

If `G` is finite, take `G' = 1`. Now let `G` be infinite with (T). Ioana's theorem applies with `Γ = Γ_0 = G`:
relative property (T) of `G ⊂ G` is property (T), and `G/G` is finitely generated. Let `s` be a lift.

1. **Untwist.** By `ioana-profinite-cocycle-superrigidity` there are `n`, a cocycle `w : G × X_n -> E` and a
   measurable `φ : X -> E` with `w(g, r_n(x)) = φ(gx) s(g,x) φ(x)^{-1}`.
2. **Level homomorphism.** `X_n` is a finite ergodic `G`-space, so `G` acts transitively on it. Fix `a ∈ X_n`, with
   stabilizer `G_a` of finite index, and `C = r_n^{-1}(a)`, of positive measure. For `h ∈ G_a` put
   `ρ(h) = w(h, a)`. The cocycle identity at the fixed point `a` makes `ρ : G_a -> E` a homomorphism.
3. **Equivariant map.** Put `ψ = π∘φ : X -> G`. Apply `π` to step 1 with `x ∈ C` and `h ∈ G_a`, using
   `π s(h,x) = h`. This gives `πρ(h) = ψ(hx) h ψ(x)^{-1}`, that is, `ψ(hx) = πρ(h) ψ(x) h^{-1}`. The formula
   `h ⋆ λ = πρ(h) λ h^{-1}` is an action of `G_a` on the set `G`:
   `h_1 ⋆ (h_2 ⋆ λ) = πρ(h_1 h_2) λ (h_1 h_2)^{-1}`. So `ψ|_C` is `G_a`-equivariant from `C` to `(G, ⋆)`.
4. **Invariant probability.** `C` is `G_a`-invariant, because `r_n(hx) = h r_n(x)`. `G_a` preserves the
   normalized restriction `μ_C`. So `ν = (ψ|_C)_* μ_C` is a `⋆`-invariant probability measure on the countable
   set `G`.
5. **Finite orbit.** `ν` is a probability measure on a countable set. So its maximal atom mass `m > 0` is
   attained, and the set `S` of points of mass `m` is finite and nonempty. `S` is `⋆`-invariant. Fix `λ_0 ∈ S`.
   Its stabilizer `G'` has index at most `|S|` in `G_a`, hence finite index in `G`.
6. **Section.** For `h ∈ G'`, `πρ(h) λ_0 h^{-1} = λ_0`, so `πρ(h) = λ_0 h λ_0^{-1}`. Choose `e_0 ∈ E` with
   `π(e_0) = λ_0`, and put `σ(h) = e_0^{-1} ρ(h) e_0` for `h ∈ G'`. Then `σ` is a homomorphism, and
   `πσ(h) = λ_0^{-1} (λ_0 h λ_0^{-1}) λ_0 = h`. So `E` splits over `G'`.

Ergodicity of `G_a` on `C` was not used, only invariance of `μ_C`.

## Step 2. Item 2: virtual splitting gives a locally constant lift

Let `σ : G' -> E` be a homomorphism with `πσ = id`, where `G'` has finite index. Put `D = σ(G')`. Then
`D ∩ A = 1`, and `[E : D] = |A| · [G : G']` is finite. Let `C` be the normal core of `D` in `E`. It is a
finite-index normal subgroup of `E` with `C ∩ A = 1`. Put `Q = E/C` and `Ḡ = G/π(C)`. Since `A ∩ C = 1`, `A`
injects into `Q`, and `Q/A ≅ E/AC ≅ Ḡ`. So `1 -> A -> Q -> Ḡ -> 1` is exact.

Hypothesis of item 2: the point stabilizers of some finite level `X_n`, which is a transitive `G`-set, lie in
`π(C)`. `π(C)` is normal, so one stabilizer suffices. Then there is a `G`-map `X_n -> Ḡ`, and composing with
`r_n` gives `x ↦ x̄` with `\overline{gx} = [g] x̄`.

1. **Choice.** Fix any map `t : Ḡ -> Q` with `t(y)` in the fibre of `Q -> Ḡ` over `y`.
2. **Definition.** For `g ∈ G` and `x ∈ X`, the element `q = t([g]x̄) t(x̄)^{-1} ∈ Q` lies over `[g]`. The lifts
   of `g` in `E` form a coset `e_1 A`. Their images in `Q` form `ē_1 A`, which is the whole fibre of `Q -> Ḡ` over
   `[g]`, and `e ↦ ē` is injective on `e_1 A` because `A` injects into `Q`. So exactly one lift `e` of `g` has
   `ē = q`. Call it `s(g,x)`.
3. **Cocycle.** `s(g,hx) s(h,x)` and `s(gh,x)` are both lifts of `gh`. Their images in `Q` are both
   `t([gh]x̄) t(x̄)^{-1}`, by telescoping. By uniqueness in step 2 they are equal.
4. **Measurability.** `s(g,x)` depends on `x` only through `r_n(x)`, so it is locally constant.

On `X = Ĝ` with levels `G/G_n`, where `G_n` runs through a decreasing cofinal chain of finite-index normal
subgroups, the finite-index normal subgroup `π(C)` contains some `G_n`. So the hypothesis holds.

## Step 3. The corollary

Throughout, `N` is a finite-index subgroup of the residually finite (T) group `G`. So `N` is residually finite,
has (T), and is finitely generated. Hence `N` has countably many finite-index subgroups and a decreasing cofinal
chain `N_n` of finite-index normal subgroups. The action of `N` on `N̂ = lim N/N_n` with Haar measure is
measure-preserving and profinite. It is ergodic because each level `N/N_n` is transitive, and it is free because
`gx = x` in the group `N̂` forces `g = 1` in `N̂`, and `N -> N̂` is injective since `N` is residually finite. `A` is a finite `N`-module,
and `E_c` is the extension attached to `c ∈ H^2(N;A)`.

1. **Inflated iff effaceable.** Continuous classes of `N̂` with finite discrete `A` are inflated from finite
   quotients `N/M`, where `M` is normal of finite index and acts trivially on `A`.
   - (⇒) If `c` is inflated from `c̄ ∈ H^2(N/M; A)` with extension `Q̄`, then `E_c ≅ Q̄ ×_{N/M} N`. The projection
     `E_c -> Q̄` is injective on `A`.
   - (⇐) If `E_c -> Q` is a finite quotient with kernel `C` and `C ∩ A = 1`, then `[C, A] ⊂ C ∩ A = 1`. So `π(C)`
     acts trivially on `A`, and `E/C` is an extension of `N/π(C)` by `A`. The map `e ↦ (eC, π(e))` into
     `(E/C) ×_{N/π(C)} N` is injective, because its kernel is `C ∩ A = 1`. It is surjective: if
     `n = π(q) π(c')` with `c' ∈ C`, then `qc'` maps to `(qC, n)`. So `E_c` is a pullback, and `c` is inflated.
2. **Effaceable iff virtually split.**
   - (⇒) If `C` is as in 1, then `π|_C` is injective. Its inverse on the finite-index subgroup `π(C)` is a section.
   - (⇐) Given a section `σ` on `G'`, the core `C` of `σ(G')` from step 2 works.
3. **Injectivity in degree two.** Let `c ∈ H^2(N̂;A)` be inflated from `H^2(N/M;A)` with extension `Q̄`, and let
   `c` die in `H^2(N;A)`. Then `Q̄ ×_{N/M} N -> N` has a section. Its composite with the projection to `Q̄` is a
   homomorphism `f : N -> Q̄` lifting `N -> N/M`. Put `M' = Ker f ⊂ M`. The induced `N/M' -> Q̄` splits the
   pullback of `Q̄` to `N/M'`. So `c` dies in `H^2(N/M';A)`, hence in `H^2(N̂;A)`. Therefore surjective
   inflation in degree two is bijective.
4. **(b) ⇒ (a).** Let `c ∈ H^2(N;A)`. By (b), `N ↷ N̂` lifts across `E_c`. By item 1 (step 1) for `N`, `E_c`
   virtually splits. By 2 and 1, `c` is inflated.
5. **(a) ⇒ (b).** An extension `E` of `N` by a finite abelian `A` makes `A` an `N`-module by conjugation, and `E`
   is `E_c` for its class `c`. By (a), `c` is inflated. By 1 and 2, `E` virtually splits. By item 2 (step 2) on
   `N̂`, `N ↷ N̂` lifts across `E`.

Steps 4 and 5 use only the one pair `(N, A)`, so the equivalence holds for each fixed pair.

## Step 4. The Deligne reading

Let `g >= 2` and let `Γ~ -> Γ = Sp_2g(Z)` be the central `Z = ⟨z⟩`-extension of
`deligne-universal-cover-lattice-is-non-rf-kazhdan`. `Γ` is residually finite and has (T), and `Γ~` is not
residually finite (items 3–4 there). Suppose that for every `n >= 2` the reduction `E_n = Γ~/⟨z^n⟩`, an extension of
`Γ` by `Z/n`, virtually splits. By step 3.2, `E_n` has a finite quotient in which `Z/n` injects, so `Γ~` has a
finite quotient in which `z` has order `n`.

Take `γ ≠ 1` in `Γ~`. If `γ ∉ ⟨z⟩`, its image in the residually finite `Γ` survives in a finite quotient. If
`γ = z^k` with `k ≠ 0`, take `n > |k|`. Either way `Γ~` would be residually finite, which is a contradiction. So
for some `n >= 2`, `E_n` does not virtually split. By item 1, `E_n` lifts across no free ergodic profinite action
of `Γ`.
