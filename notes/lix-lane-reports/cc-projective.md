# Lane `cc-projective`

Owns `GroupApproximation/CharClass/{ProjectiveSpace*,LerayHirsch*,Chern*}.lean`,
namespace `GroupApproximation.CharClass`.  Deliverables: §1.4 items 1–4 of
`notes/LIX_FULL_PROGRAM_2026-09-05.md`.

## Module plan

| module | content | depends on |
|---|---|---|
| `ChernRelation.lean` | pure algebra of `ξ^r + γ₁ξ^{r-1}+⋯+γ_r = 0`: `chernPoly` = `PowerBasis.minpolyGen`, uniqueness, `chernClass`, rank bound, naturality under base change, split case `γ_k = e_k(y)`, Whitney reduced to an injective base change | Mathlib only |
| `ProjectiveSpaceCover.lean` | point-set half of item 1 over `Analysis/LIXProjectiveSpaceModel`'s `CP d`: chart `ℂ^d ≃ chartSet`, hyperplane `CP d ↪ CP (d+1)`, puncture, deformation retract `CP(d+1) ∖ pt ≃ CP d`, `chartSet ∩ punctured ≃ S^{2d+1}` | `Analysis/LIXProjectiveSpaceModel` |
| `ProjectiveSpaceCohomology.lean` | `H^k(CP d; F₂)` by MV induction; the degree-2 generator `h_d`; stability under `CP d ⊆ CP (d+1)` | `cc-cohom-api` |
| `LerayHirschAlgebra.lean` | the module-theoretic core of the LH induction (five lemma in element form, `PowerBasis` assembly from a spanning + free family) | Mathlib only |
| `LerayHirschLine.lean` | LH for `P(L ⊕ 1)`; Gysin of `S(L)` | `cc-bundle`, `cc-cohom-api` |
| `ProjectiveSpaceRing.lean` | `H^*(CP n;F₂) = F₂[h]/(h^{n+1})` from Gysin with `S(taut) = S^{2n+1}` | above |
| `LerayHirschGeneral.lean` | LH for `P(E)`, rank `r`, compact base; Künneth with `CP n` | above |
| `ChernClasses.lean` | `γ_i(E)` for a projection-model bundle; naturality; `γ(L) = X + e(L)`; MvN invariance | above |
| `ChernSplitting.lean` | flag bundle, injectivity on `H^*`, Whitney, `γ_i(⊕L_k) = e_i(e(L_k))` | above |

## GREEN

*(nothing yet — first probe in flight)*

## AUTHORED, UNVERIFIED

* `GroupApproximation/CharClass/ChernRelation.lean` — pure algebra, Mathlib only.

## NEEDS

From `cc-cohom-api` (`CharClass/Cohomology*.lean`):

```lean
-- element-level cup, already present in the vendored tree as `cupZMod2`; what I need
-- packaged is the EVEN TOTAL RING, because `TotalChern`/`Polynomial` need a `CommRing`:
def evenRing (X : TopCat.{0}) : Type          -- ⊕_{n} H^{2n}(X; F₂)
instance (X : TopCat.{0}) : CommRing (evenRing X)
def evenRing.of {X : TopCat.{0}} {n : ℕ} (a : cohomologyZMod2 X (2 * n)) : evenRing X
def evenRing.map {X Y : TopCat.{0}} (f : X ⟶ Y) : evenRing Y →+* evenRing X
theorem evenRing.map_of ... ; evenRing.map_id ; evenRing.map_comp
-- and the graded-piece injectivity `evenRing.of` is injective on each degree.
```

plus, in element form:

```lean
def cup {X} {p q} : cohomologyZMod2 X p → cohomologyZMod2 X q → cohomologyZMod2 X (p+q)
theorem cup_assoc / cup_comm (mod 2) / one_cup / cup_one / cohPullback_cup
-- Mayer–Vietoris in element form for two opens U V with U ∪ V = X:
theorem mv_exact_* : the six-term exactness at each spot, in `Function.Exact` form
def mvDelta (U V) (k) : cohomologyZMod2 (U ∩ V) k → cohomologyZMod2 X (k+1)
theorem mvDelta_cup_restrict :   -- H^*(X)-linearity of δ
    mvDelta U V (a ⌣ (restrict b)) = (mvDelta U V a) ⌣ b       -- b global
-- Künneth with spheres and `H^k(S^n;F₂)`.
-- Homotopy invariance in element form: a homotopy equivalence induces a bijection.
```

From `cc-bundle` (`CharClass/Bundle*.lean`): the projective bundle `P(p)` as a
subspace of `X × CP (K-1)`, the tautological line on it, `P(p) ⊆ P(p ⊕ 1)`,
`E(p) = P(p⊕1) ∖ P(p)`, the zero section, the finite trivializing cover with the
local homeomorphisms `P(p)|_U ≅ U × CP^{r-1}`, and MvN invariance.

## TRAPS

*(none recorded yet)*
