import GroupApproximation.CharClass.RelativeSmallChains
import GroupApproximation.CharClass.CohomologyAssoc

/-!
# The cup product of two relative cochains vanishes on small chains

The mechanism behind the splitting of a Chern polynomial over a cover is one
combinatorial fact about the Alexander--Whitney formula.  If `α` kills every
simplex lying in `U` and `β` kills every simplex lying in `V`, then on a simplex
that lies in *either* one the product `α(front) · β(back)` vanishes: a front face
of a simplex in `U` lies in `U`, and a back face of one in `V` lies in `V`.

Both halves of that are the same lemma, because both faces have range contained
in the range of the simplex.  What distinguishes them is only which factor is
killed.

The conclusion is about *small* simplices, not all of them, and that is not a
weakness of the argument but its shape: a general simplex meets both sets and the
product genuinely need not vanish on it.  Passing from small chains to classes is
`RelativeSmallChains`, already on `origin/main`, which is why nothing here
subdivides anything.

## Main declarations

* `isSubordinate_frontSimplex`, `isSubordinate_backSimplex` — the two faces stay
  inside whatever the simplex is inside.
* `cochainCup_eval_eq_zero_of_subordinate` — **the combinatorial core**.
* `pairCover` — a two-member open cover.
* `cochainCup_mem_smallAnn` — the product kills every small simplex.
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

noncomputable section

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. The two Alexander–Whitney faces stay inside -/

/-- The front face, as a continuous map: precomposition with the realisation of
`frontFace`.  The naturality lemma it uses is general in the simplex-category
map, so this is the same one line as the boundary-face version. -/
theorem frontSimplex_continuousMap (X : TopCat.{0}) (p q : ℕ)
    (σ : singularSimplices X (p + q)) :
    singularSimplexAsContinuousMap X p (frontSimplex X p q σ)
      = (singularSimplexAsContinuousMap X (p + q) σ).comp
          (SimplexCategory.toTop₀.map (frontFace p q)).hom := by
  rw [singularSimplexAsContinuousMap, singularSimplexAsContinuousMap, frontSimplex,
    toSSetObjEquiv_map_op_naturality X p (p + q) (frontFace p q) σ]

/-- The back face, as a continuous map. -/
theorem backSimplex_continuousMap (X : TopCat.{0}) (p q : ℕ)
    (σ : singularSimplices X (p + q)) :
    singularSimplexAsContinuousMap X q (backSimplex X p q σ)
      = (singularSimplexAsContinuousMap X (p + q) σ).comp
          (SimplexCategory.toTop₀.map (backFace p q)).hom := by
  rw [singularSimplexAsContinuousMap, singularSimplexAsContinuousMap, backSimplex,
    toSSetObjEquiv_map_op_naturality X q (p + q) (backFace p q) σ]

/-- **A front face of a simplex inside `S` is inside `S`.** -/
theorem isSubordinate_frontSimplex {S : Set X} {p q : ℕ}
    {σ : singularSimplices X (p + q)} (hσ : IsSubordinate S σ) :
    IsSubordinate S (frontSimplex X p q σ) :=
  hσ.comp_of_range_subset (SimplexCategory.toTop₀.map (frontFace p q)).hom
    (frontSimplex_continuousMap X p q σ)

/-- **A back face of a simplex inside `S` is inside `S`.** -/
theorem isSubordinate_backSimplex {S : Set X} {p q : ℕ}
    {σ : singularSimplices X (p + q)} (hσ : IsSubordinate S σ) :
    IsSubordinate S (backSimplex X p q σ) :=
  hσ.comp_of_range_subset (SimplexCategory.toTop₀.map (backFace p q)).hom
    (backSimplex_continuousMap X p q σ)

/-! ## 2. The combinatorial core -/

/-- **The core.**  On a simplex lying in `U` or in `V`, the cup product of a
`U`-vanishing cochain and a `V`-vanishing cochain is zero.  Which of the two
factors dies depends on which set the simplex lies in, and nothing else. -/
theorem cochainCup_eval_eq_zero_of_subordinate {U V : Set X} {p q : ℕ}
    {α : singularCochainGroup R X p} {β : singularCochainGroup R X q}
    (hα : α ∈ relCochainSubmodule R X U p) (hβ : β ∈ relCochainSubmodule R X V q)
    (σ : singularSimplices X (p + q)) (hσ : IsSubordinate U σ ∨ IsSubordinate V σ) :
    cochainEval (p + q) (cochainCup p q α β) σ = 0 := by
  rw [cochainCup_eval]
  rcases hσ with h | h
  · rw [hα _ (isSubordinate_frontSimplex h), zero_mul]
  · rw [hβ _ (isSubordinate_backSimplex h), mul_zero]

/-! ## 3. Against a two-member cover -/

/-- The open cover with exactly two members. -/
def pairCover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) : OpenCoverData X where
  sets := {U, V}
  isOpen_mem := fun W hW => by
    have hW' : W = U ∨ W = V := hW
    rcases hW' with rfl | rfl
    · exact hU
    · exact hV
  covers := fun x => by
    rcases hUV x with h | h
    · exact ⟨U, Or.inl rfl, h⟩
    · exact ⟨V, Or.inr rfl, h⟩

/-- **The product kills every small simplex.**  A simplex small for the two-member
cover lies in one of them, which is exactly the hypothesis of the core. -/
theorem cochainCup_mem_smallAnn {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) {p q : ℕ}
    {α : singularCochainGroup R X p} {β : singularCochainGroup R X q}
    (hα : α ∈ relCochainSubmodule R X U p) (hβ : β ∈ relCochainSubmodule R X V q) :
    cochainCup p q α β ∈ smallAnnSubmodule R X (pairCover U V hU hV hUV) (p + q) := by
  intro σ hσ
  obtain ⟨W, hW, hsub⟩ := hσ
  have hW' : W = U ∨ W = V := hW
  refine cochainCup_eval_eq_zero_of_subordinate hα hβ σ ?_
  rcases hW' with rfl | rfl
  · exact Or.inl hsub
  · exact Or.inr hsub

end

end GroupApproximation.CharClass
