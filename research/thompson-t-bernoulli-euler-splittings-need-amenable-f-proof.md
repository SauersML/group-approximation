---
rg: 2
id: thompson-t-bernoulli-euler-splittings-need-amenable-f-proof
kind: route
title: "Untwist the circle cocycle on the commuting copies F_A x F_B by Popa's spectral-gap theorem, spread the untwisting along overlapping arcs to all of T-bar, and let perfectness kill the value on z"
target: thompson-t-bernoulli-euler-splittings-need-amenable-f
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation as in the target.

**Imports.**
- (P) Popa, *On the superrigidity of malleable actions with spectral gap*, J. Amer. Math. Soc.
  21 (2008), arXiv:math/0608429. Theorem 1.1 and Corollary 1.2 were read in the arXiv text on
  2026-09-18. Corollary 1.2, verbatim:

  > Let Γ be a countable group having infinite commuting subgroups H, H′ with H non-amenable.
  > Let Γ ↷ X be an m.p. action whose restriction to HH′ is a relative weak mixing quotient of
  > one of the following: 1°. A generalized Bernoulli action HH′ ↷ (X0, µ0)^I, with the actions
  > of H, H′ on the countable set I satisfying |H′i| = ∞ and {g ∈ H | gi = i} amenable, ∀i ∈ I.
  > 2°. A Gaussian action associated to an orthogonal representation of HH′ which has stable
  > spectral gap on H and no finite dimensional H′-invariant subspaces. If H′ is w-normal in Γ,
  > then Γ ↷ X is U_fin-cocycle superrigid.

  - "U_fin-cocycle superrigid" means that every cocycle with values in a closed subgroup `V` of
    the unitary group of a separable finite von Neumann algebra is cohomologous to a
    homomorphism `Γ → V`. This includes separable compact `V`, such as `S^1` (p. 3 of the
    source).
  - "w-normal" allows `H′` normal in `Γ`, via the one-step chain `H′ ⊂ Γ`.
- (I1) `T̄` is perfect: `lifted-thompson-t-perfect-centre-cubically-elliptic`, item 2.
- (I2) For a dyadic arc `J` with nonempty interior, `F_J ≅ F`. In particular `F_J` is
  infinite. This is standard (Cannon–Floyd–Parry, the same fact as (I2) of that node's proof).
- (I3) Standard ergodic theory.
  - A generalized Bernoulli action of a group `S` over an `S`-set with all orbits infinite is
    mixing, hence weakly mixing.
  - The Gaussian action of an orthogonal representation with no finite-dimensional invariant
    subspace is weakly mixing.
  - A weakly mixing pmp action has no nonconstant measurable eigenfunction `h` with `|h| = 1`
    and `h(sx) = λ_s h(x)`.

Throughout, `θ ∈ R \ Z` and `w : T̄ × X → S^1` is a measurable cocycle:
`w(gh, x) = w(g, hx) w(h, x)` a.e. for each pair `g, h`, and `w(z, ·) = e^{2πiθ}` a.e.
Item 2 of the target follows from item 1 applied to `w = e^{2πiθβ}`.

## Step 1. Canonical lifts

Write `p : R → S^1 = R/Z`. For `f ∈ F_J`, let `f̃ ∈ T̄` be the lift of `f` that is the identity on
`p^{-1}(S^1 \ J)`.

**It exists and is unique.**
- `S^1 \ J` is a nonempty open arc, and `f` is the identity on it.
- The lifts of `f` are `f̂ z^k` for `k ∈ Z`. Exactly one of them fixes a chosen point `y_0` over
  `S^1 \ J`.
- That lift maps the component `U` of `p^{-1}(S^1 \ J)` containing `y_0` into `p^{-1}(S^1 \ J)`
  continuously, lifting the identity. So it is the identity on `U`.
- It commutes with `z`, so it is the identity on every translate `U + n`. These translates are
  all of `p^{-1}(S^1 \ J)`.

Write `F̃_J = {f̃ : f ∈ F_J}`. It has the following properties.

- (a) *Subgroup.* `f ↦ f̃` is an injective homomorphism `F_J → T̄`. The product `f̃ g̃` lifts
  `fg` and is the identity on `p^{-1}(S^1 \ J)`.
- (b) *Monotone.* If `J ⊆ J'` then `F̃_J ⊆ F̃_{J'}`. For `f ∈ F_J`, `f̃` is the identity on
  `p^{-1}(S^1 \ J') ⊆ p^{-1}(S^1 \ J)`.
- (c) *Equivariant.* For `g ∈ T̄` with `t = π(g)`, `g^{-1} F̃_J g = F̃_{t^{-1}J}`.
  - `g^{-1} f̃ g` lifts `t^{-1} f t ∈ F_{t^{-1}J}`.
  - If `p(y) ∉ t^{-1}J`, then `p(g y) = t p(y) ∉ J`. So `f̃` fixes `g y`, and
    `g^{-1} f̃ g y = y`.
  - Hence `g^{-1} f̃ g` is the canonical lift.
- (d) *Commuting pair.* `F̃_A` and `F̃_B` commute, and `L̄ = F̃_A F̃_B` maps isomorphically onto
  `L = F_A F_B = F_A × F_B`.
  - Let `f ∈ F_A` and `g ∈ F_B`. Then `c = [f̃, g̃]` lifts `[f, g] = 1`, because the supports
    have disjoint interiors. So `c = z^k`.
  - Take `y` over the interior of `B`. `f̃` fixes `p^{-1}(int B)` pointwise, since
    `int B ⊆ S^1 \ A`.
  - `g` fixes the endpoints of `B`, so `g̃` preserves each component of `p^{-1}(int B)`, and so
    does `g̃^{-1}`. Hence `c y = f̃ g̃ f̃^{-1} g̃^{-1} y = y`, and `k = 0`.
  - `F_A ∩ F_B = {1}`, because an element in both is the identity off `A ∩ B = {0, 1/2}`.
  - If `f̃ g̃ = z^k`, then `fg = 1`, so `f = g = 1` and `k = 0`. So `π|_{L̄}` is injective.

## Step 2. Untwisting on `L̄`

`L̄` acts on `X` through the isomorphism `π|_{L̄} : L̄ → L`. Apply Corollary 1.2 of (P) with
`Γ = HH′ = L̄`, `H = F̃_A` and `H′ = F̃_B`. The hypotheses hold as follows.

- `H`, `H′` are infinite and commute (Step 1(d), (I2)).
- `H ≅ F_A ≅ F` is nonamenable. This is the hypothesis of the target, with (I2).
- `H′` is normal in `Γ = H × H′`, hence w-normal.
- *(Ber).* The restriction to `L̄` is itself the generalized Bernoulli action `L̄ ↷ X_0^I`.
  - `Stab_H(i) = Stab_{F_A}(i)` is amenable.
  - `|H′ i| = |F_B i| = ∞`, by the orbit hypothesis with `J = B`.
  - A system is trivially a relative weak mixing quotient of itself.
- *(Gau).* The restriction is the Gaussian action of `ρ|_L`.
  - It has stable spectral gap on `F_A`.
  - It has no finite-dimensional `F_B`-invariant subspace (the hypothesis with `J = B`).

So `w|_{L̄}` is cohomologous to a homomorphism. There are a measurable `u : X → S^1` and a
homomorphism `δ : L̄ → S^1` with

```text
w(l, x) = u(lx) δ(l) conj(u(x))   for all l ∈ L̄ and a.e. x.        (U)
```

Popa writes this as `u(lx)^* δ(l) u(x)`. The two forms differ by replacing `u` with `ū`, which
is harmless because `S^1` is abelian.

## Step 3. The untwisting set is a subgroup containing `L̄` and `z`

Fix `u` from (U). Let `S` be the set of `g ∈ T̄` for which some constant `c_g ∈ S^1` satisfies

```text
w(g, x) = u(gx) c_g conj(u(x))   for a.e. x.                          (S)
```

- The constant `c_g` is unique, because `|u| = 1`.
- *Subgroup.* If `g, h ∈ S`, the cocycle identity gives
  - `w(gh, x) = u(ghx) c_g conj(u(hx)) · u(hx) c_h conj(u(x)) = u(ghx) c_g c_h conj(u(x))`.
  - So `gh ∈ S` and `c_{gh} = c_g c_h`.
  - Also `1 = w(1, x) = w(g^{-1}, gx) w(g, x)`, which gives `g^{-1} ∈ S` with
    `c_{g^{-1}} = conj(c_g)`.
  - So `S` is a subgroup and `c : S → S^1` is a homomorphism.
- *`L̄ ⊆ S`*, by (U), with `c = δ` on `L̄`.
- *`z ∈ S` with `c_z = e^{2πiθ}`.* `z` acts trivially on `X`, so `u(zx) = u(x)`, and
  `w(z, x) = e^{2πiθ}`.

The a.e. substitutions `x ↦ hx` are legitimate because each `h` preserves `μ`, and `T̄` is
countable.

## Step 4. Spreading along overlaps

**Lemma.** Let `g ∈ T̄` and `t = π(g)`. If `B ∩ t^{-1}B` has nonempty interior, then `g ∈ S`.

*Proof.*
- *An infinite subgroup of `S ∩ g^{-1} S g`.* Choose a dyadic arc `J ⊆ B ∩ t^{-1}B` with nonempty
  interior.
  - By Step 1(b), `F̃_J ⊆ F̃_B ⊆ L̄ ⊆ S`.
  - By Step 1(b) and (c), `F̃_J ⊆ F̃_{t^{-1}B} = g^{-1} F̃_B g ⊆ g^{-1} S g`.
- *An eigenfunction.* Put `h(x) = w(g, x) conj(u(gx)) u(x)`, so `|h| = 1`. Let `s ∈ F̃_J` and
  `s′ = g s g^{-1}`, so `s′ ∈ S`. Evaluate `w(gs, x) = w(s′g, x)` both ways:
  - `w(g, sx) w(s, x) = w(g, sx) u(sx) c_s conj(u(x))`;
  - `w(s′, gx) w(g, x) = u(s′gx) c_{s′} conj(u(gx)) w(g, x) = u(gsx) c_{s′} conj(u(gx)) w(g, x)`.
  - Multiply both sides by `conj(u(gsx)) u(x)`. This gives
    `h(sx) c_s = c_{s′} h(x)`, that is, `h(sx) = c_{s′} conj(c_s) h(x)` for a.e. `x`.
- *Weak mixing.* `F̃_J` acts on `X` through `F_J ≅ F` (I2), which is infinite.
  - *(Ber).* Every `F_J`-orbit on `I` is infinite, so `F_J ↷ X_0^I` is mixing (I3).
  - *(Gau).* `ρ|_{F_J}` has no finite-dimensional invariant subspace, so the Gaussian action of
    `F_J` is weakly mixing (I3).
  - Either way, the eigenfunction `h` is a.e. constant, say `h ≡ c` (I3).
- Then `w(g, x) = u(gx) c conj(u(x))`, so `g ∈ S`. ∎

## Step 5. The overlaps generate `T̄`

Let `Q = {t ∈ T : B ∩ t^{-1}B has nonempty interior}`. By Step 4, `π^{-1}(Q) ⊆ S`.
- *Small rotations.* Let `r_a(x) = x + a` for dyadic `a` with `|a| < 1/2`. Then
  `r_a^{-1}B = [−a, 1/2 − a]` meets `B = [0, 1/2]` in an arc of length `1/2 − |a| > 0`. So
  `r_a ∈ Q`.
- *The stabilizer of 0.* If `t(0) = 0`, then `t^{-1}B = [0, t^{-1}(1/2)]`, because `t` is an
  orientation-preserving homeomorphism fixing `0`. Its intersection with `B` is
  `[0, min(1/2, t^{-1}(1/2))]`, which has nonempty interior. So `Stab_T(0) ⊆ Q`.
- *Every `t ∈ T`.* `a = t(0) ∈ [0, 1)` is dyadic, and `t = r_{a/2}^2 ∘ (r_{−a} ∘ t)`.
  - `r_{a/2} ∈ Q`, since `|a/2| < 1/2`.
  - `r_{−a} ∘ t` fixes `0`, so it lies in `Q`.
  - So `⟨Q⟩ = T`.
- *Lifting.* `1 ∈ Q`, so `ker π = ⟨z⟩ ⊆ π^{-1}(Q)`. Hence `⟨π^{-1}(Q)⟩ = π^{-1}(⟨Q⟩) = T̄`.

Therefore `S = T̄`.

## Step 6. Conclusion

- `c : T̄ → S^1` is a homomorphism (Step 3) into an abelian group.
- `T̄` is perfect (I1), so `c ≡ 1`.
- But `c_z = e^{2πiθ} ≠ 1`, because `θ ∉ Z`. This is a contradiction, which proves item 1.
- For item 2, a measurable Euler splitting `β` would give the cocycle `w = e^{2πiθβ}` with
  `w(z, ·) = e^{2πiθ}`. This contradicts item 1.
- The equivalence with survival of `e_R` in `H²(T; L⁰(X, R))` is the standard dictionary.
  - Let `rot~` be the translation-number quasimorphism on `T̄`, so `rot~(zg) = rot~(g) + 1`.
    Then `c(g, h) = rot~(ĝ) + rot~(ĥ) − rot~(ĝĥ)` is a bounded 2-cocycle on `T`, independent
    of the lifts, and it represents `e_R`.
  - If a measurable `b : T × X → R` satisfies `db = −c`, then `b(1, ·) = 0`, and
    `β(g, x) = b(π(g), x) + rot~(g)` is a measurable Euler splitting.
  - Conversely, `b(t, x) = β(ĝ, x) − rot~(ĝ)` for any lift `ĝ` of `t` satisfies `db = −c`. ∎

## Scope and checks

- *Where `F` nonamenable is used.* Only in Step 2, for `H = F̃_A`. Everything else is
  unconditional.
- *Not covered.*
  - Nonsingular or infinite-measure witnesses.
  - Counting-measure witnesses `T/H`. These are not mixing, and `F`-orbits on them can be
    finite.
  - Generalized Bernoulli spaces over a `T`-set `I` with some finite `F_J`-orbit. An example
    is any `T`-invariant `I ⊆ S^1`, such as the dyadic points, because `F_J` fixes every
    point outside `J`.
  - pmp spaces that are neither Bernoulli nor Gaussian over `F_A × F_B`.
- *Sanity check.* The argument does not show that `T̄` fails the Haagerup property, and it
  could not. It uses only one pmp space at a time, and (MT) is only sufficient for Haagerup.
