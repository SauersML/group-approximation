import GroupApproximation.CharClass.CartanSingular
import GroupApproximation.CharClass.CartanGroupRing

/-!
# The singular boundary with coefficients in a `ZMod 2`-algebra

The target of Steenrod's diagonal, `S(X) ⊗ S(X)`, is a free module over the group
ring on pairs of singular simplices, so its differential is built from the
singular boundary **with group-ring coefficients**.  `CartanSingular.lean` gives
the boundary with `ZMod 2` coefficients, and `∂∂ = 0` for free from Mathlib's
alternating face map complex.  This file moves both across.

## The transfer is nearly free

`∂` is a sum of `Finsupp.lmapDomain`s along the face maps, so it is defined over
any coefficient ring by the same formula.  Pushing coefficients along
`algebraMap : ZMod 2 → Λ` is additive and sends `single σ 1` to `single σ 1`, so
it carries the `ZMod 2` boundary to the `Λ` boundary (`bdU_coeffPush`); and a sum
of basis elements that vanishes over `ZMod 2` therefore vanishes over `Λ`.  That
is the whole content of `bdU_bdU`: no simplicial identity, no pairing argument
over `Fin (n+2) × Fin (n+3)`, just Mathlib's `d_comp_d` pushed forward.

The same transfer discharges any other characteristic-two identity between sums
of basis elements, which is why it is stated here as a lemma about `coeffPush`
rather than inlined.
-/

namespace GroupApproximation.CharClass

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 1. Pushing coefficients along the structure map -/

variable (Λ : Type) [CommRing Λ]

/-! ### The boundary over `Λ` -/

/-- The mod-2 singular boundary with coefficients in `Λ`: the unsigned sum of
the face maps.  The formula makes sense over any coefficient ring, which is what
makes the transfer below possible. -/
def bdU (X : TopCat.{0}) (n : ℕ) :
    (singularSimplices X (n + 1) →₀ Λ) →ₗ[Λ] (singularSimplices X n →₀ Λ) :=
  ∑ i : Fin (n + 2), Finsupp.lmapDomain Λ Λ (faceSimplex X n i)

theorem bdU_single (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X (n + 1)) :
    bdU Λ X n (Finsupp.single σ (1 : Λ))
      = ∑ i : Fin (n + 2), Finsupp.single (faceSimplex X n i σ) (1 : Λ) := by
  rw [bdU, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The boundary with `ZMod 2` coefficients, read off the singular chain
complex, where `∂∂ = 0` is already known. -/
def bdTwo (X : TopCat.{0}) (n : ℕ) :
    (singularSimplices X (n + 1) →₀ ZMod 2) →ₗ[ZMod 2] (singularSimplices X n →₀ ZMod 2) :=
  ((singFree.obj X).d (n + 1) n).hom

theorem bdTwo_single (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X (n + 1)) :
    bdTwo X n (Finsupp.single σ (1 : ZMod 2))
      = ∑ i : Fin (n + 2), Finsupp.single (faceSimplex X n i σ) (1 : ZMod 2) :=
  singFree_d_single X n σ

theorem bdTwo_bdTwo (X : TopCat.{0}) (n : ℕ)
    (c : singularSimplices X (n + 2) →₀ ZMod 2) :
    bdTwo X n (bdTwo X (n + 1) c) = 0 := by
  show ((singFree.obj X).d (n + 1) n).hom
      (((singFree.obj X).d (n + 2) (n + 1)).hom c) = 0
  have h := HomologicalComplex.d_comp_d (singFree.obj X) (n + 2) (n + 1) n
  have h2 := congrArg
    (fun u : (singFree.obj X).X (n + 2) ⟶ (singFree.obj X).X n => u.hom c) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h2

/-! ### The coefficient push -/

variable [Algebra (ZMod 2) Λ]

/-- Push `ZMod 2` coefficients into a `ZMod 2`-algebra. -/
def coeffPush {ι : Type} : (ι →₀ ZMod 2) →+ (ι →₀ Λ) :=
  Finsupp.mapRange.addMonoidHom (algebraMap (ZMod 2) Λ).toAddMonoidHom

theorem coeffPush_apply {ι : Type} (c : ι →₀ ZMod 2) (x : ι) :
    coeffPush Λ c x = algebraMap (ZMod 2) Λ (c x) := rfl

@[simp] theorem coeffPush_single {ι : Type} (x : ι) :
    coeffPush Λ (Finsupp.single x (1 : ZMod 2)) = Finsupp.single x (1 : Λ) := by
  ext y
  rw [coeffPush_apply]
  by_cases h : x = y
  · subst h
    simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm h), Finsupp.single_eq_of_ne (Ne.symm h),
      map_zero]

/-! ## 2. The transfer -/

/-- The boundary commutes with pushing coefficients forward. -/
theorem bdU_coeffPush (X : TopCat.{0}) (n : ℕ)
    (c : singularSimplices X (n + 1) →₀ ZMod 2) :
    bdU Λ X n (coeffPush Λ c) = coeffPush Λ (bdTwo X n c) := by
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp
  · intro a b ha hb
    rw [map_add, map_add, map_add, ha, hb, map_add]
  · intro x y
    rcases zmod2_eq_zero_or_one y with hy | hy
    · rw [hy, Finsupp.single_zero]
      simp
    · rw [hy, coeffPush_single, bdU_single, bdTwo_single, map_sum]
      exact Finset.sum_congr rfl fun i _ => (coeffPush_single Λ _).symm

/-- **`∂ ∘ ∂ = 0` over `Λ`**, transferred from `ZMod 2` with no simplicial
identity and no pairing argument. -/
theorem bdU_bdU (X : TopCat.{0}) (n : ℕ)
    (c : singularSimplices X (n + 2) →₀ Λ) :
    bdU Λ X n (bdU Λ X (n + 1) c) = 0 := by
  have key : (bdU Λ X n).comp (bdU Λ X (n + 1)) = 0 := by
    apply Finsupp.lhom_ext'
    intro σ
    apply LinearMap.ext_ring
    show bdU Λ X n (bdU Λ X (n + 1) (Finsupp.single σ (1 : Λ))) = 0
    rw [← coeffPush_single Λ σ, bdU_coeffPush, bdU_coeffPush, bdTwo_bdTwo, map_zero]
  have h2 := congrArg (fun F : (singularSimplices X (n + 2) →₀ Λ) →ₗ[Λ]
    (singularSimplices X n →₀ Λ) => F c) key
  simpa using h2

end

end GroupApproximation.CharClass
