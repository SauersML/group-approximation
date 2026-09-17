---
rg: 2
id: sparse-full-group-kazhdan-pair-proof
kind: route
title: Bernoulli-extend over the Γ-orbit relation, prove mixing from sparsity, lift the pair, and feed it to the full-group certificate
target: sparse-full-group-kazhdan-pair-gives-mixing-nonsofic-action
requires:
  - full-group-kazhdan-pair-noninvariant-fixed-algebra-is-nonsofic
---

Discard a null set so that `G` acts freely on `X`, and so that `ρ` is an honest action by Borel automorphisms, each
`ρ(l)` piecewise a translation by elements of `G`. Write `R = R_G` and `R' = R_(ρ(Γ)) ⊆ R`.

**Step 0: construction.** Enumerate `G = {g_0 = e, g_1, …}`. For `x ∈ X` and `h ∈ G` let `n(h,x)` be the least `i` with
`g_i x R' hx`. The classes of `[x]_R / R'` are labeled by the set `N(x) = {n(h,x) : h ∈ G} ⊆ ℕ`.

* `Y` is the Borel bundle over `X` with fiber `{0,1}^(N(x))`, with measure `μ` times fair product measure on each fiber.
  It is standard: pad with independent unused coordinates to realize it as a Borel subset of `X × {0,1}^ℕ` modulo
  unused coordinates.
* The fiber over `x` is intrinsically `{0,1}^([x]_R/R')`, and `[gx]_R/R' = [x]_R/R'`. So `g(x,ω) = (gx, ω)` is
  well defined, Borel (reindex through `n(·,·)`) and measure-preserving.
* The coordinate functions `b_h(x,ω) = ω([hx]_(R'))`, `h ∈ G`, together with `L^∞(X)`, generate the σ-algebra of `Y`.
  Moreover `b_h ∘ g^(-1) = b_(hg^(-1))`, since `g^(-1)(x,ω) = (g^(-1)x, ω)` and `[hg^(-1)x]` is the class of that point.

**Step 1: freeness.** `g(x,ω) = (x,ω)` forces `gx = x`, so `g = e` for a.e. `x`.

**Step 2: mixing.** Let `𝒞` be the span of the functions

```text
Φ(x,ω) = F(x) ∏_(h ∈ A) c_h( b_h(x,ω) ),     F ∈ L^∞(X), A ⊆ G finite, c_h : {0,1} → ℂ.
```

`𝒞` is a unital *-algebra generating the σ-algebra, hence dense in `L^2(Y)`. Mixing for a dense set of vectors
implies mixing, since the Koopman representation is unitary. So it suffices to show
`∫ (Φ∘g^(-1)) Ψ → ∫Φ ∫Ψ` for `Φ` as above (data `F, A, c`) and `Ψ` with data `F', B, c'`.

*Conditional expectation onto the base.* For fixed `x` the coordinates `ω(C)`, `C ∈ [x]_R/R'`, are independent fair
coins. So

```text
E(Φ | X)(x) = F(x) I_A(x),      I_A(x) = ∏_(classes C of {hx : h ∈ A} modulo R')  𝔼_ξ ∏_(h ∈ A, hx ∈ C) c_h(ξ),
```

where `ξ` is a fair coin. `I_A` is Borel and bounded by `∏ ||c_h||_∞`.

*The product.* `(Φ∘g^(-1))(x,ω) = F(g^(-1)x) ∏_(h∈A) c_h(ω([hg^(-1)x]))`. Let

```text
E_g = {x : hg^(-1)x R' kx for some h ∈ A, k ∈ B}.
```

For `x ∉ E_g`, the coordinates read by the two products lie in disjoint sets of classes. The fiber integral
factorizes:

```text
𝔼_ω[(Φ∘g^(-1))Ψ](x) = F(g^(-1)x) I_A(g^(-1)x) · F'(x) I_B(x).
```

The partition of `{hg^(-1)x : h ∈ A}` into `R'`-classes is the partition defining `I_A(g^(-1)x)`.

*Sparsity bounds `E_g`.* `hg^(-1)x R' kx` means `hg^(-1)x ∈ ρ(Γ)kx`. Substituting `y = kx`, which preserves `μ`:

```text
μ(E_g) <= Σ_(h∈A, k∈B) μ{y : (hg^(-1)k^(-1)) y ∈ ρ(Γ) y} = Σ_(h,k) p(hg^(-1)k^(-1)).
```

As `g → ∞` with `A, B` fixed, every `hg^(-1)k^(-1) → ∞`, so `μ(E_g) → 0` by (a).

*Conclusion.* With `M = ||Φ||_∞ ||Ψ||_∞`,

```text
| ∫ (Φ∘g^(-1)) Ψ  −  ∫ (F I_A)∘g^(-1) · F' I_B dμ |  <=  2M μ(E_g) → 0.
```

Mixing of `G ↷ X` gives `∫ (F I_A)∘g^(-1) · F' I_B → ∫ F I_A ∫ F' I_B = ∫Φ ∫Ψ`. So `G ↷ Y` is mixing.

**Step 3: lifting the pair.** For `l ∈ L` put `ρ̃(l)(x,ω) = (ρ(l)x, ω)`. This is well defined, because
`[ρ(l)x]_R/R' = [x]_R/R'`, and it is a homomorphism. On the Borel piece `{x : ρ(l)x = gx} × fibers` it agrees with
the translation `g`, so `ρ̃(l) ∈ [R_(G ↷ Y)]`.

**Step 4: the fixed algebra is not invariant.**

* Let `f = b_e`, i.e. `f(x,ω) = ω([x]_(R'))`. Since `[ρ(γ)x]_(R') = [x]_(R')`, `f` is `ρ̃(Γ)`-invariant.
* Take `l, γ` from (b) and put `f' = f ∘ ρ̃(l^(-1))`, i.e. `f'(x,ω) = ω([ρ(l^(-1))x]_(R'))`. With `y = ρ(l^(-1))x`,

```text
(f' ∘ ρ̃(γ))(x,ω) = ω([ρ(l^(-1)γl) y]_(R')).
```

* On `D = {x : ρ(l^(-1)γl)y ∉ ρ(Γ)y}` the two classes `[ρ(l^(-1)γl)y]` and `[y]` differ. So `f'∘ρ̃(γ)` and `f'` read
  two independent fair coins, and `||f'∘ρ̃(γ) − f'||_2^2 = μ(D)/2`.
* `ρ(l^(-1))` preserves `μ`, so `μ(D)` equals the measure in (b), which is positive.

Hence `f ∈ L^∞(Y)^(ρ̃(Γ))` but `f ∘ ρ̃(l^(-1)) ∉ L^∞(Y)^(ρ̃(Γ))`, so the fixed algebra is not `ρ̃(L)`-invariant.

**Step 5: nonsoficity.** `G ↷ Y` is essentially free (Step 1), and `ρ̃ : L → [R_(G↷Y)]` is a homomorphism with
`Γ <= L` Kazhdan, `Γ` infranormal and `L` sofic (Step 3), and a non-invariant fixed algebra (Step 4). By
`full-group-kazhdan-pair-noninvariant-fixed-algebra-is-nonsofic`, `G ↷ Y` is not sofic. It is mixing (Step 2), and
`G` is sofic by hypothesis. ∎

**Step 6: the automatic cases.**

1. *Finite `ρ(Γ)`-orbits give (a).* By freeness, `Σ_g 1[gx ∈ ρ(Γ)x] = |ρ(Γ)x|`. Tonelli gives
   `Σ_g μ{gx ∈ ρ(Γ)x, |ρ(Γ)x| <= N} <= N`, so that term tends to `0` as `g → ∞`. Hence
   `limsup p(g) <= μ{|ρ(Γ)x| > N}`, which tends to `0` as `N → ∞`.
2. *Free `ρ` and non-normal `Γ` give (b).* Some `l` has `l^(-1)Γl ⊄ Γ`: if `l^(-1)Γl ⊆ Γ` for every `l`, applying
   this to `l^(-1)` gives equality and `Γ` is normal. Pick `γ` with `l^(-1)γl ∉ Γ`. If
   `ρ(l^(-1)γl)y = ρ(γ')y` for some `γ' ∈ Γ`, then `γ'^(-1)l^(-1)γl` fixes `y`. By freeness and countability of `Γ`,
   this happens only on a null set.
3. *Subgroups of `G` kill (a).* If `ρ(Γ)` contains translations by an infinite subgroup `H <= G`, then `p(h) = 1`
   for `h ∈ H`. With `ρ = id` this is the generalized Bernoulli action of Kun--Thom, which is not mixing.
4. *Finite `ρ(L)`-orbits kill (b).* On a finite `ρ(L)`-orbit the image of `Γ` is normal in the image of `L`
   (`haagerup-hosts-blind-full-group-kazhdan-certificate-proof`, Step 6). So `ρ(l^(-1)γl)y ∈ ρ(Γ)y` everywhere.
5. *Untwisting kills (a).* Let `c : Γ × X → G` be the cocycle `ρ(γ)x = c(γ,x)x`. Suppose `ρ(Γ)` is mixing,
   `X` is nonatomic, and `c(γ,x) = φ(ρ(γ)x)^(-1) δ(γ) φ(x)` for a homomorphism `δ : Γ → G` and a Borel
   `φ : X → G`. Let `ν = φ_*μ`.
   * *`ker δ` finite.* Pick `a, b` with `ν(a), ν(b) > 0`. On `{φ(x) = b, φ(ρ(γ)x) = a}` we have
     `ρ(γ)x = a^(-1)δ(γ)b·x`. By mixing that set has measure `→ ν(a)ν(b)` as `γ → ∞`. Since `ker δ` is finite,
     `a^(-1)δ(γ)b → ∞`, and `p` stays `>= ν(a)ν(b)/2` along it.
   * *`K = ker δ` infinite.* `ρ(K)` is mixing, hence ergodic. For `γ ∈ K`, `ρ(γ)x = φ(ρ(γ)x)^(-1)φ(x)·x`. If `ν` had
     finite support, `ρ(K)`-orbits would be finite, which is impossible for an ergodic action on a nonatomic space.
     So `supp ν` is infinite. For `a, b ∈ supp ν`, ergodicity sends a.e. `x ∈ φ^(-1)(b)` into `φ^(-1)(a)` by some
     `ρ(γ)`, `γ ∈ K`, and that point is `a^(-1)b·x`. So `p(a^(-1)b) >= ν(b)`, and `a^(-1)b → ∞` as `a → ∞` in `supp ν`.

   By Popa's cocycle superrigidity (`popa-bernoulli-cocycle-superrigidity`), if `Γ` is Kazhdan and `ρ(Γ)` is a
   Bernoulli action, every such cocycle is cohomologous to a homomorphism. Such `ρ(Γ)` never satisfy (a).
6. *Finite `ρ(Γ)`-orbits kill (b) where they occur.* Let `n(y) = |ρ(Γ)y| ∈ ℕ ∪ {∞}`.
   * *Compressors do not shrink orbits.* Let `g ∈ L` with `gΓg^(-1) <= Γ`. Then `ρ(g)` maps `ρ(Γ)y` bijectively onto
     `ρ(gΓg^(-1))ρ(g)y ⊆ ρ(Γ)ρ(g)y`, so `n <= n∘ρ(g)`.
   * *Monotone functions are invariant.* `ρ(g)` preserves `μ`, so for each `t` the sets `{n∘ρ(g) >= t} ⊇ {n >= t}` have
     equal measure and agree a.e. Hence `n∘ρ(g) = n` a.e.
   * *Γ-orbits map onto Γ-orbits.* Where `n < ∞`, the inclusion `ρ(g)ρ(Γ)y ⊆ ρ(Γ)ρ(g)y` is between sets of equal finite
     size, so it is an equality. Thus on the set `F = {n < ∞}`, which is invariant under `ρ(g)` up to null sets,
     `ρ(g)` and `ρ(g)^(-1)` map `ρ(Γ)`-orbits onto `ρ(Γ)`-orbits.
   * *All of `L` permutes them.* Compressors generate `L` (infranormality), so every `ρ(l)` maps `ρ(Γ)`-orbits in `F`
     onto `ρ(Γ)`-orbits. So `ρ(l^(-1)γl)y ∈ ρ(l^(-1))ρ(Γ)ρ(l)y = ρ(Γ)y` for a.e. `y ∈ F`.

   So the set in (b) lies, up to a null set, in the part where `ρ(Γ)`-orbits are infinite. Together with (a), a sparse
   pair needs infinite `ρ(Γ)`-orbits that occupy vanishing density of every `G`-direction.

**Step 7: tightness into Haagerup groups.** Let `Γ` be Kazhdan, acting p.m.p. on `(Z,λ)`, and `β : Γ × Z → M` a Borel
cocycle into a countable Haagerup group. Steps 1--2 of `haagerup-hosts-blind-full-group-kazhdan-certificate-proof` use
neither freeness nor range bounds. They give `φ_t ∈ C_0(M)` and an invariant `η` with `||ξ̂ − η|| <= δ`. Hence
`|Φ_t(γ) − ⟨η, ξ̂⟩| <= δ` and `|1 − ⟨η, ξ̂⟩| <= δ`, so `Re Φ_t(γ) >= 1 − 2δ` for all `γ`. Let `F = {|φ_t| >= 1/2}`,
which is finite. Then

```text
1 − 2δ <= μ{β(γ,·) ∈ F} + (1/2)(1 − μ{β(γ,·) ∈ F}),
```

so `μ{β(γ,·) ∈ F} >= 1 − 4δ` for every `γ`. With `δ = 1/8`, for every `γ` some `m_γ ∈ F` has `μ{β(γ,·) = m_γ} >= 1/(2|F|)`.
So `sup_m μ{β(γ,·) = m} >= 1/(2|F|)` for all `γ`, and anti-concentration fails. In the twisted product design
(`G = L × M` acting freely, `ρ(l)x = (l, β(l,x))x`, with `Z = X` and `Γ` acting through `ρ`), `ρ(γ')x = (γ, m)x`
means `(γ', β(γ',x))x = (γ,m)x`, which by freeness of `G` forces `γ' = γ` and `β(γ,x) = m`. So
`p((γ, m)) = μ{β(γ,·) = m}` for `γ ∈ Γ`. Since
`(γ, m_γ) → ∞` as `γ → ∞`, (a) fails.

**Step 8: untwisting in the twisted product design.** Assume `ρ(Γ)` is mixing. Suppose
`β(γ,x) = ψ(ρ(γ)x)^(-1) δ(γ) ψ(x)` for `γ ∈ Γ`, with `δ : Γ → M` a homomorphism and `ψ : X → M` Borel. Let
`ν = ψ_*μ` and pick `a, b` with `ν(a), ν(b) > 0`. On `{ψ = b} ∩ ρ(γ)^(-1){ψ = a}`, `β(γ,·) = a^(-1)δ(γ)b`. So

```text
sup_m μ{β(γ,·) = m} >= μ({ψ = b} ∩ ρ(γ)^(-1){ψ = a}) → ν(a)ν(b) > 0      as γ → ∞,
```

by mixing of `ρ(Γ)`. So (a) fails.

*Where Popa applies.* Suppose `ρ` is the Bernoulli action `([0,1],Leb)^L`. Restricted to `Γ`, it is the
Bernoulli action of `Γ` with diffuse base `([0,1],Leb)^(Γ\L)`, which is s-malleable and weakly mixing. `Γ` is
Kazhdan, so by `popa-bernoulli-cocycle-superrigidity` (applied to `Γ` with `H = Γ`), `β|Γ` is cohomologous to a
homomorphism, and (a) fails. The same argument covers every s-malleable `Γ`-action that is mixing.
