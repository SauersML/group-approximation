---
rg: 2
id: bieri-strebel-line-rigidity-proof
kind: route
title: Finitely many of Bieri--Strebel's order-dependent conjugation relations survive every nearby deformation, while the rest detect the sign of every breakpoint, so nearby deformations are homotheties
target: fp-bieri-strebel-line-groups-are-deformation-rigid
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

Lane proof, not independently reviewed. Source for the presentation: Bieri--Strebel, *On groups
of PL-homeomorphisms of the real line*, arXiv:1411.2868v3. Used are Proposition D13.1 (book p. 75),
Proposition D13.3 (p. 76) and the presentation of §13.3a, relations (13.23)--(13.25) (pp. 80--81).
All were read at source. Functions compose right to left, and `^x y = x y x^{-1}`.
`g(a,p)` is the identity on `(-∞,a]` and `t ↦ p(t-a)+a` on `[a,∞)`.

## Step 1: a finite presentation with finitely many order relations

Let `G` be finitely presented. Then `G` is finitely generated, so `P` is finitely generated and
`A` is a finitely generated `Z[P]`-module (Theorem B7.1), and `P` is free abelian with a basis
`𝒫 = {π_1, …, π_m}`, `m ≥ 1`. By D13.3, `Aff(A,P)` is finitely presented. Fix finite `Z[P]`-module
generators `𝒜 = {a_1, …, a_s}` of `A` with `a_1 ≠ 0`. §13.3a (from D13.1) gives the presentation of
`G` on the finite set `𝒳 = {f(p), g(p) : p ∈ 𝒫} ∪ {h(a) : a ∈ 𝒜}`, where `f(p) = aff(0,p)`,
`g(p) = g(0,p)` and `h(a) = aff(a,1)`, with relators:
- **(13.23)** a finite presentation of `Aff(A,P)` on `f(𝒫) ∪ h(𝒜)`. For `b ∈ A`, `h(b)` is
  written as a fixed word `η_b`, a product of conjugates `^{f(q)} h(a)^{±1}` read off from an
  expression `b = Σ ±q_ℓ a_ℓ`.
- **(13.24)** `[f(p), g(p')] = 1 = [g(p), g(p')]` for `p, p' ∈ 𝒫`.
- **(13.25)** `R_{b,p,p'}: ^{g(p) η_b} g(p') = ^{f(p) η_b} g(p')`, for `b ∈ A_{>0}` and
  `p, p' ∈ 𝒫`.

Since `G` is finitely presented and `𝒳` is finite, finitely many of these relators already
define `G` (B. H. Neumann). So there are `b_1, …, b_k ∈ A_{>0}` such that (13.23), (13.24) and
the `R_{b_i,p,p'}` define `G`. We may take `k ≥ 1`.

## Step 2: evaluating the generators at a deformation

For `(χ, α) ∈ D(A,P)`, set `f(p)' = aff(0, χ(p))`, `g(p)' = g(0, χ(p))` and
`h(a)' = aff(α(a), 1)`. Then:
- **(13.23) holds.** The map `A ⋊ P → Aff(R)`, `(a,p) ↦ (t ↦ χ(p) t + α(a))`, is a homomorphism,
  because `α` is additive and `α(pa) = χ(p) α(a)`. So every relator of `Aff(A,P)` evaluates to
  the identity, and `η_b` evaluates to the translation `aff(α(b), 1)`.
- **(13.24) holds.** Homotheties and the maps `g(0,·)` fix `0` and are linear on each half-line.
- **`R_b` for `α(b) > 0` holds.** `^{η_b'} g(p')' = g(α(b), χ(p'))`. Conjugating by `g(p)'` gives
  `g(χ(p)α(b), χ(p'))`, because `g(p)'` is the homothety `χ(p)` on `[0,∞) ∋ α(b)`. Conjugating
  by `f(p)'` gives the same map.
- **`R_b` for `α(b) < 0` fails when `χ(p), χ(p') ≠ 1`.** The left side
  `^{g(p)'} g(α(b), χ(p'))` is the identity on `(-∞, α(b)]` and has slope `χ(p') ≠ 1` just to
  the right of `α(b)`, since there all points are still negative and `g(p)'` is the identity.
  The right side is `g(χ(p)α(b), χ(p'))`, whose only breakpoint `χ(p)α(b)` differs from `α(b)`.

Let `U = {(χ, α) : α(b_i) > 0 for i ≤ k, χ(π_1) ≠ 1}`. It is open, since each `α(b_i)` is a
fixed Laurent polynomial in the coordinates `α(a_ℓ)`, `χ(π_j)`, and it contains `ι`. For
`(χ,α) ∈ U` every defining relator of Step 1 holds for the primed maps. So von Dyck gives a
homomorphism `φ: G → Homeo(R)` sending each generator to its primed version. Every relator of
`G`, in particular every `R_{b,π_1,π_1}` with `b ∈ A_{>0}`, therefore holds for the primed maps.
By the last bullet, **`α(b) ≥ 0` for every `b ∈ A` with `b > 0`**.

## Step 3: monotone deformations are homotheties

Let `(χ, α) ∈ U`. `α` is additive and weakly monotone on `A ⊂ R`. Fix `a_0 ∈ A_{>0}` and put
`c = α(a_0)/a_0 ≥ 0`. For `x ∈ A` and integers `m, n` with `n > 0`:
- if `m a_0 < n x`, then `α(nx - m a_0) ≥ 0`, so `α(x) ≥ (m/n) c a_0`;
- if `m a_0 > n x`, then `α(x) ≤ (m/n) c a_0`.

Letting `m/n → x/a_0` gives `α(x) = c x`. Also `c > 0`, because `α(b_1) > 0`. Then for
`p ∈ P` and `a ≠ 0`, `χ(p) c a = α(pa) = c p a`, so `χ(p) = p`. Hence `U ⊆ R_{>0}·ι`, which
proves the Theorem. ∎

## Step 4: corollaries

**Corollary 2 (and 3).** Let `β ∈ Hom_{Z[P]}(A, R)`. For small `ε`, `(incl, incl + εβ)` lies in
`D(A,P)` and in `U`, since the finitely many conditions are open. So `incl + εβ = c·incl`, and
`β ∈ R·incl`. Now let `K = Q(P) ⊂ R`, and let `V = K·A ⊂ R` be the `K`-span of `A`, of dimension
`d`. Every `K`-linear map `V → R` restricts to an element of `Hom_{Z[P]}(A,R)`, and distinct maps
restrict distinctly because `A` spans `V`. So `R^d ≅ Hom_K(V,R)` embeds in `R·incl`, which forces
`d = 1`, i.e. `A ⊆ K·a` for any nonzero `a ∈ A`. For a nontrivial splitting `A = M_1 ⊕ M_2`,
`β = incl` on `M_2` and `0` on `M_1` would be a map not in `R·incl`, so `A` is indecomposable.
If `P ⊂ Q`, then `K = Q`.

**Corollary 1 (Tarski).** Rescale so that `a_1 = 1`. The coordinates `(x_ℓ, y_j) = (α(a_ℓ), χ(π_j))`
identify `D(A,P)` with
`{(x,y) ∈ R^s × R^m_{>0} : Σ_ℓ c_{rℓ}(y) x_ℓ = 0 for all r}`. Here the `c_{rℓ} ∈ Z[y^{±1}]` are
finitely many generators of the relation module of `A` over the noetherian ring `Z[P]`. Put
`D_1 = D(A,P) ∩ {x_1 = 1}`. It is a semialgebraic set defined over `Q`, and by the Theorem
`ι` is an isolated point of `D_1`. A semialgebraic set has finitely many connected components, so
its isolated points form a finite semialgebraic set defined over `Q`. Its points are then
definable over `Q` in the real field. Since the real algebraic numbers form an elementary
substructure (Tarski), their coordinates are real algebraic. So each `π_j` is algebraic. ∎

## Remarks

- Only the sign behavior of (13.25) is used. What makes the line group sensitive to deformations
  is that its presentation mentions the order of `A` (as Remark D13.2 notes) and fixes nothing else.
- For the example `A = Z[1/2] + Z[1/2]τ`, `P = gp(2)` of the target, the proof is explicit.
  `α(u + wτ) = u + wτ'` is a deformation for every real `τ'`. If `τ' < τ`, take a dyadic
  `u ∈ (-τ, -τ')` and `b = u + τ`. If `τ' > τ`, take `u ∈ (τ, τ')` and `b = u - τ`. Either
  way `b > 0 > α(b)`.
