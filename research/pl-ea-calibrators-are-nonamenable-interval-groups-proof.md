---
rg: 2
id: pl-ea-calibrators-are-nonamenable-interval-groups-proof
kind: route
title: Real-valued breakpoint lamps, Følner sets of the germ group pushed to the infimum of an orbit, and the rotation number of an invariant measure
target: pl-ea-calibrators-are-nonamenable-interval-groups
requires: [affine-lamplighter-amenable-iff-extensively-amenable, thompson-t-orbits-carry-no-invariant-means, f-dyadic-ea-iff-inverted-orbit-confinement, pl-plus-interval-has-no-non-abelian-free-subgroups]
---

**Imported statements.**
- JMBMdlS (arXiv:1503.04977) Definition 1.1 and Lemma 2.1, verbatim in the required claim
  `affine-lamplighter-amenable-iff-extensively-amenable`: "Every action of an amenable group is extensively
  amenable, and every extensively amenable action on a nonempty set is amenable."
- JMBMdlS functor statements, quoted verbatim (arXiv source read on 2026-09-17) in
  `thompson-f-amenable-iff-dyadic-action-extensively-amenable-proof`:
  - Verbatim 1: a functor `I → Amen` extends to all sets by direct limits.
  - Verbatim 2: for amenable `A`, the functor `Y ↦ A^Y` has `F(X) = A^{(X)}`.
  - Verbatim 3, which we use: "Let $G \acts X$ be an extensively amenable action and let
    $F\colon \cati \to \cata$ be any functor. A subgroup $H$ of $F(X) \rtimes G$ is amenable as soon as the
    intersection $H \cap (\{1\} \times G)$ is so."

  Verbatim 3 makes no transitivity assumption.
- The JMBMdlS inverted-orbit proposition, verbatim in `f-dyadic-ea-iff-inverted-orbit-confinement-proof`. Its
  hypotheses: `G` finitely generated and acting transitively, `μ` symmetric with generating support.

## Item 1. Breakpoint equivalence

Let `G ≤ PL_+(I)` or `G ≤ PL_+(S^1)`.
- For `g ∈ G` and each point `x`, the one-sided derivatives `g'(x^±) > 0` exist. On the circle they are read
  through a lift.
- Put `β(g)(x) = log g'(x^+) − log g'(x^-)`. This is a finitely supported real function with support `bp(g)`.
- Let `G` act on functions by `(k·φ)(x) = φ(k^{-1}x)`.

Every `h ∈ G` preserves orientation. So the chain rule gives `(fh)'(x^±) = f'(h(x)^±) h'(x^±)`, that is
`β(fh) = h^{-1}·β(f) + β(h)` (R).

*Invariance of `B = B(G)`.* By (R), `h^{-1}·β(f) = β(fh) − β(h)`. Its support is `h^{-1}(bp f)`, which lies in
`bp(fh) ∪ bp(h) ⊆ B`. As `f` and `h` range over `G`, `h^{-1}(B) ⊆ B` for all `h`, so `B` is `G`-invariant.

*Embedding.*
- `β(g) ∈ R^{(B)}`. The additive group `R`, taken discrete, is abelian and hence amenable.
- By Verbatims 1–2, `Y ↦ R^Y` is a functor `I → Amen` with value `R^{(B)}` on `B`.
- Functoriality induces the action `(g·φ)(x) = φ(g^{-1}x)` on `R^{(B)}`.
- Put `c_g = β(g^{-1})`. By (R), `c_{gh} = β(h^{-1}g^{-1}) = g·β(h^{-1}) + β(g^{-1}) = c_g + g·c_h`.
- So `ι(g) = (c_g, g)` is an injective homomorphism `G → R^{(B)} ⋊ G`, with law `(a,g)(b,h) = (a + g·b, gh)`.

*Kernel.* Put `H = ι(G)`. Then `H ∩ ({0} × G) ≅ {g : c_g = 0}`, the set of `g` with `bp(g^{-1}) = ∅`.
- Interval case: `g^{-1}` is affine and fixes `0` and `1`, so `g = id`.
- Circle case: a lift of `g^{-1}` is an affine map `x ↦ ax + b` commuting with `x ↦ x+1`. So `a = 1` and `g` is a
  rotation.

Either way the intersection is isomorphic to a group of rotations. It is abelian, hence amenable.

*Conclusion.*
- (⇒) Lemma 2.1.
- (⇐) Suppose `G ↷ B` is EA. By Verbatim 3, `H ≅ G` is amenable. ∎

## Item 2. Orbit actions of interval groups are amenable

Let `G ≤ PL_+(I)` and let `Y ⊆ I` be nonempty and `G`-invariant. Put `b = inf Y`. Each `g ∈ G` is an increasing
bijection of `I` with `g(Y) = Y`, so `g(b) = inf g(Y) = b`.

*Case `b ∈ Y`.* The Dirac mean at `b` is invariant.

*Case `b ∉ Y`.*
- Then `b < 1`, and `Y ∩ (b, b+ε) ≠ ∅` for every `ε > 0`.
- Each `g` fixes `b` and has finitely many breakpoints. So there are `ε_g > 0` and `σ(g) > 0` with
  `g(x) = b + σ(g)(x − b)` on `[b, b+ε_g]`.
- `σ` is a homomorphism. For `x` close to `b`, `h(x) ∈ [b, b+ε_g]` by continuity, so
  `gh(x) = b + σ(g)σ(h)(x−b)`.
- `Γ = σ(G) ≤ R_{>0}` is abelian, hence amenable as a discrete group.

Fix a finite `S ⊆ G` and `δ > 0`.
- Choose a finite nonempty `A ⊆ Γ` with `|σ(s)A Δ A| ≤ δ|A|` for all `s ∈ S`.
- For each `α ∈ A ∪ σ(S)A`, choose `g_α ∈ G` with `σ(g_α) = α`.
- Choose `z ∈ Y` so close to `b` that `z ≤ b + ε_{g_α}` for all these `α`, and `b + α(z−b) ≤ b + ε_s` for all
  `α ∈ A` and `s ∈ S`.
- Put `π(α) = b + α(z − b)`. Then `π(α) = g_α(z) ∈ Y`, and `s(π(α)) = π(σ(s)α)` for `α ∈ A`, `s ∈ S`.
- Let `ν = π_*(u_A)`, where `u_A` is uniform on `A`. This is a probability measure on `Y`, and
  `s_*ν = π_*(u_{σ(s)A})`.
- Pushing forward does not increase the `ℓ^1` norm, so `‖s_*ν − ν‖_1 ≤ |σ(s)A Δ A|/|A| ≤ δ`.

Index these measures by pairs `(S, δ)`. A weak-* cluster point in `ℓ^∞(Y)^*` is a `G`-invariant mean on `Y`.
Injectivity of `π` is not needed. ∎

This is the mechanism of `thompson-f-end-rigid-schreier-graphs-are-amenable`, with the germ group at the infimum
of the orbit in place of the powers of `x_0`.

## Item 3. Circle groups with an amenable orbit action

Let `G ≤ PL_+(S^1)`, and let `m` be a `G`-invariant mean on a nonempty `G`-invariant `Y ⊆ S^1`.

*Invariant measure.*
- `I(φ) = m(φ|_Y)` is a positive unital linear functional on `C(S^1)`. By Riesz it is integration against a Borel
  probability measure `μ`.
- `Y` is invariant, so `(φ∘g)|_Y = (φ|_Y)∘g|_Y`. Invariance of `m` gives `∫ φ∘g dμ = ∫ φ dμ`, so `g_*μ = μ`.

*Rotation number.*
- Let `G̃` be the group of lifts of elements of `G` to `R`, and `μ̃` the `Z`-periodic lift of `μ`.
- A lift `g̃` covers a `μ`-preserving map, so it preserves `μ̃`. On Borel sets inside intervals of length `< 1`,
  `μ̃` is `μ` transported by the local inverse of the projection. Countable additivity extends this.
- Put `Φ(t) = μ̃([0,t))` for `t ≥ 0` and `Φ(t) = −μ̃([t,0))` for `t < 0`. Then `Φ` is nondecreasing,
  `Φ(t+1) = Φ(t) + 1`, and `Φ(t) − Φ(s) = μ̃([s,t))` for `s ≤ t`.
- `g̃` maps `[s,t)` onto `[g̃s, g̃t)` and preserves `μ̃`, so `Φ(g̃t) − Φ(g̃s) = Φ(t) − Φ(s)`.
- Hence `τ(g̃) = Φ(g̃t) − Φ(t)` does not depend on `t`.
- `τ` is additive: `τ(g̃h̃) = (Φ(g̃h̃t) − Φ(h̃t)) + (Φ(h̃t) − Φ(t)) = τ(g̃) + τ(h̃)`.
- `τ(t ↦ t+1) = 1`. So `τ` descends to a homomorphism `rot : G → R/Z`.

*Kernel fixes the support.*
- Let `g ∈ K = ker rot`. Choose the lift `g̃` with `τ(g̃) = 0`.
- Let `x ∈ supp μ` with lift `x̃`, and suppose `g̃x̃ > x̃`. By continuity choose `s < x̃` with `g̃s > x̃`.
- Then `μ̃([s, g̃s)) = Φ(g̃s) − Φ(s) = τ(g̃) = 0`. Since `μ̃([s,s+1)) = 1`, this forces `g̃s < s + 1`.
- So `(s, g̃s)` projects injectively to an open neighbourhood of `x` of `μ`-measure `0`. This contradicts
  `x ∈ supp μ`.
- The case `g̃x̃ < x̃` is the same with `g̃^{-1}`. So `g̃x̃ = x̃` and `gx = x`.

Hence `K` fixes `supp μ ≠ ∅` pointwise.

*Structure.*
- Pick `p ∈ supp μ` and put `ψ(t) = p + t mod 1` on `[0,1]`. Each `k ∈ K` fixes `p`, so `ψ^{-1}kψ` (fixing `0`
  and `1`) is in `PL_+(I)`. This gives an injective homomorphism `K → PL_+(I)`.
- `G/K ↪ R/Z` is abelian. So `G` is amenable iff `K` is: amenability passes to subgroups and to extensions by
  abelian groups.
- Suppose `F_2 ≤ G`. Then `[F_2, F_2] ≤ K`, and `[F_2,F_2]` is a non-abelian free group (Nielsen–Schreier;
  `[a,b]` and `[a^2,b]` do not commute). This contradicts `pl-plus-interval-has-no-non-abelian-free-subgroups`. ∎

*Remark on the circle worlds named in the claim.* If `G` contains a dense group of rotations, an invariant `μ`
has Fourier coefficients `μ̂(k) = e^{2πikθ} μ̂(k)` for a dense set of `θ`. So `μ̂(k) = 0` for `k ≠ 0`, and `μ` is
Lebesgue measure. A single element of `G` that does not preserve Lebesgue measure then shows that no orbit action
of `G` is amenable.

## Item 4. The dichotomy

(b) ⇒ (a).
- Amenability is local: a group is amenable iff its finitely generated subgroups are. So a nonamenable subgroup of
  `PL_+(I)` contains a finitely generated, hence countable, nonamenable `G`.
- `G ≠ 1` and `bp(g) = ∅` forces `g = id`, so `B(G) ≠ ∅`.
- By item 2, `G ↷ B(G)` is amenable. By item 1, it is not EA.

(a) ⇒ (b).
- Let `G` be as in (a). By item 1, `G` is nonamenable.
- In the interval case, `G` itself is the required subgroup.
- In the circle case, item 3 with `Y = B(G)` gives `K ↪ PL_+(I)` with `G/K` abelian. So `K` is nonamenable. ∎

## Item 5. Thompson's T

Let `G ≤ T` contain `r_{1/4}`, `r_{1/2}` and `x_0`, and let `Y ⊆ S^1` be nonempty and `G`-invariant.

*Not amenable, not EA.*
- If `G ↷ Y` were amenable, the first step of item 3 would give a Borel probability measure invariant under
  `r_{1/4}`, `r_{1/2}` and `x_0`. Item 2 of `thompson-t-orbits-carry-no-invariant-means` says no such measure
  exists.
- So `G ↷ Y` is not amenable. By the second half of Lemma 2.1, it is not EA.

*Instances.*
- `Y = D/Z` with `G = T`.
- `T` acts transitively on `D/Z` through the dyadic rotations. `Stab_T(0)` consists of the dyadic PL maps of the
  circle fixing `0`, that is `F`. So `T/F ≅ D/Z` as `T`-sets, and `F` is not co-amenable in `T`.

*Inverted orbit.*
- `G_3 = ⟨r_{1/4}, r_{1/2}, x_0⟩` is finitely generated and acts transitively on `Y = G_3·0`, and `G_3 ↷ Y` is
  not EA.
- By the JMBMdlS inverted-orbit proposition, condition (ii) fails: there is `ε > 0` with
  `P(|O_n| < εn) ≤ e^{−εn}` for all but finitely many `n`. ∎

## Scope and honesty

- Items 1–4 are proved above from the imported statements and elementary measure theory. The rotation-number
  argument is written out rather than cited.
- The "What this calibrates and kills" section of the claim is a consequence of items 1–5 together with Lemma 2.1
  (EA implies amenable action). It asserts no literature status. It says only that no nonamenable subgroup of
  `PL_+(I)` is recorded in the graph.
- Item 1 is presumably folklore for anyone who knows JMBMdlS. No priority is claimed.
