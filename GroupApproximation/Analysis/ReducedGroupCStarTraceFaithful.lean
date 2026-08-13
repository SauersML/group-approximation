import GroupApproximation.Analysis.FaithfulTracialState
import GroupApproximation.Analysis.ReducedGroupCStarTrace

/-!
# Faithfulness of the canonical reduced-group trace

This file proves the operator-algebraic facts deliberately separated from the
construction of the concrete reduced group C⋆-algebra.  Right translations
commute with its left-regular generators, hence with their norm closure.  This
makes the identity vector separating.  Expanding a vector in the point-mass
basis gives the convolution formula for the identity coefficient, from which
traciality follows by the inversion bijection.
-/

open scoped ENNReal InnerProductSpace ComplexOrder

namespace GroupApproximation

namespace ReducedGroupCStarTrace

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

instance reducedGroupCStarSubalgebra_isClosed :
    IsClosed (reducedGroupCStarSubalgebra G :
      Set (GroupHilbert G →L[ℂ] GroupHilbert G)) :=
  StarSubalgebra.isClosed_topologicalClosure _

/-- The right regular unitary.  Our convention is
`(ρ(g)f)(x) = f(xg⁻¹)`, so `ρ(g)δ₁ = δ_g`. -/
def rightRegular (g : G) : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert G :=
  lpCongrLeft (Equiv.mulRight g)

@[simp]
theorem rightRegular_apply (g : G) (f : GroupHilbert G) (x : G) :
    rightRegular G g f x = f (x * g⁻¹) :=
  rfl

/-- The right regular unitary as a bounded operator. -/
def rightRegularOperator (g : G) : GroupHilbert G →L[ℂ] GroupHilbert G :=
  rightRegular G g

@[simp]
theorem rightRegularOperator_apply (g : G) (f : GroupHilbert G) (x : G) :
    rightRegularOperator G g f x = f (x * g⁻¹) :=
  rfl

/-- Left and right regular translations commute. -/
theorem leftRegularOperator_comm_rightRegularOperator (g h : G) :
    leftRegularOperator G g * rightRegularOperator G h =
      rightRegularOperator G h * leftRegularOperator G g := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  simp only [mul_apply_eq_comp, leftRegularOperator_apply,
    rightRegularOperator_apply]
  rw [mul_assoc]

/-- The adjoint of a right translation is translation by the inverse. -/
theorem star_rightRegularOperator (g : G) :
    star (rightRegularOperator G g) = rightRegularOperator G g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint (rightRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change f (x * g) = f (x * (g⁻¹)⁻¹)
  rw [inv_inv]

/-- Every element of the reduced group C⋆-algebra commutes with every right
translation. -/
theorem reduced_commutes_right (T : ReducedGroupCStar G) (g : G) :
    (T : GroupHilbert G →L[ℂ] GroupHilbert G) * rightRegularOperator G g =
      rightRegularOperator G g * (T : GroupHilbert G →L[ℂ] GroupHilbert G) := by
  let C : StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) :=
    StarSubalgebra.centralizer ℂ ({rightRegularOperator G g} : Set _)
  have hgen : StarAlgebra.adjoin ℂ (Set.range (leftRegularOperator G)) ≤ C := by
    apply StarAlgebra.adjoin_le
    rintro L ⟨h, rfl⟩
    change leftRegularOperator G h ∈
      StarSubalgebra.centralizer ℂ ({rightRegularOperator G g} : Set _)
    rw [StarSubalgebra.mem_centralizer_iff]
    intro R hR
    have hR' : R = rightRegularOperator G g := Set.mem_singleton_iff.mp hR
    subst R
    constructor
    · exact (leftRegularOperator_comm_rightRegularOperator G h g).symm
    · rw [star_rightRegularOperator]
      exact (leftRegularOperator_comm_rightRegularOperator G h g⁻¹).symm
  have hclosed : IsClosed (C : Set (GroupHilbert G →L[ℂ] GroupHilbert G)) := by
    rw [StarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  have hclosure : reducedGroupCStarSubalgebra G ≤ C :=
    StarSubalgebra.topologicalClosure_minimal hgen hclosed
  have hmem := hclosure T.property
  rw [StarSubalgebra.mem_centralizer_iff] at hmem
  exact (hmem (rightRegularOperator G g) (Set.mem_singleton _)).1.symm

/-- Right translation sends the identity point mass to the point mass at its
group parameter. -/
theorem rightRegular_deltaOne (g : G) :
    rightRegularOperator G g (deltaOne G) = lp.single 2 g 1 := by
  apply lp.ext
  funext x
  simp only [rightRegularOperator_apply, deltaOne, lp.coeFn_single]
  by_cases hx : x = g
  · subst x
    simp
  · have hne : x * g⁻¹ ≠ 1 := by
      intro h
      apply hx
      calc x = (x * g⁻¹) * g := by simp
        _ = g := by rw [h, one_mul]
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hx]

/-- A reduced-group operator acts on a point mass by translating its action
on the identity point mass. -/
theorem apply_single (T : ReducedGroupCStar G) (g : G) (c : ℂ) :
    (T : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g c) =
      c • rightRegularOperator G g
        ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) := by
  have hsingle : lp.single 2 g c =
      c • (lp.single 2 g (1 : ℂ) : GroupHilbert G) := by
    rw [← lp.single_smul]
    simp
  rw [hsingle, map_smul, ← rightRegular_deltaOne]
  congr 1
  have hcomm := reduced_commutes_right G T g
  exact DFunLike.congr_fun hcomm (deltaOne G)

/-- The identity coefficient of a product is the convolution of the two
identity columns. -/
theorem hasSum_product_coefficient (T S : ReducedGroupCStar G) :
    HasSum
      (fun g : G ↦
        ((S : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g *
          ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g⁻¹)
      (ambientCoefficientAtOne G
        ((T : GroupHilbert G →L[ℂ] GroupHilbert G) *
          (S : GroupHilbert G →L[ℂ] GroupHilbert G))) := by
  let evalAfterT : GroupHilbert G →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : G ↦ ℂ) 2 (1 : G)).comp
      (T : GroupHilbert G →L[ℂ] GroupHilbert G)
  have hs := (lp.hasSum_single ENNReal.ofNat_ne_top
    ((S : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))).mapL evalAfterT
  convert hs using 1
  · ext g
    dsimp only [evalAfterT, ContinuousLinearMap.comp_apply]
    change
      ((S : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g *
          ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g⁻¹ =
        ((T : GroupHilbert G →L[ℂ] GroupHilbert G)
          (lp.single 2 g
            ((S : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G) g))) 1
    rw [apply_single]
    change
      ((S : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g *
          ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g⁻¹ =
        ((S : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) g *
          (rightRegularOperator G g
            ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))) 1
    rw [rightRegularOperator_apply]
    simp only [one_mul]
  · rfl

/-- The canonical coefficient is tracial on the reduced group C⋆-algebra. -/
theorem canonicalCoefficientAtOne_mul_comm (T S : ReducedGroupCStar G) :
    canonicalCoefficientAtOne G (T * S) = canonicalCoefficientAtOne G (S * T) := by
  have hTS := hasSum_product_coefficient G T S
  have hST := hasSum_product_coefficient G S T
  have hSTinv := (Equiv.inv G).hasSum_iff.mpr hST
  apply hTS.unique
  convert hSTinv using 1
  · ext g
    simp only [Function.comp_apply, Equiv.inv_apply, inv_inv]
    rw [mul_comm]
  · rfl

/-- The identity coefficient of `T⋆T` is the squared norm of `Tδ₁`. -/
theorem canonicalCoefficientAtOne_star_mul_self (T : ReducedGroupCStar G) :
    canonicalCoefficientAtOne G (star T * T) =
      ‖(T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖ ^ 2 := by
  change
    (((star (T : GroupHilbert G →L[ℂ] GroupHilbert G)) *
      (T : GroupHilbert G →L[ℂ] GroupHilbert G)) (deltaOne G)) 1 = _
  calc
    _ = ⟪deltaOne G,
        ((star (T : GroupHilbert G →L[ℂ] GroupHilbert G)) *
          (T : GroupHilbert G →L[ℂ] GroupHilbert G)) (deltaOne G)⟫_ℂ := by
      rw [deltaOne, lp.inner_single_left]
      simp
    _ = _ := by
      simp only [mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
      rfl

/-- The identity vector separates the concrete reduced group C⋆-algebra. -/
theorem eq_zero_of_apply_deltaOne_eq_zero (T : ReducedGroupCStar G)
    (hT : (T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G) = 0) : T = 0 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  have hs := (lp.hasSum_single ENNReal.ofNat_ne_top f).mapL
    (T : GroupHilbert G →L[ℂ] GroupHilbert G)
  have hzero : ∀ g : G,
      (T : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g (f g)) = 0 := by
    intro g
    rw [apply_single, hT, map_zero, smul_zero]
  have hz : HasSum
      (fun g : G ↦
        (T : GroupHilbert G →L[ℂ] GroupHilbert G) (lp.single 2 g (f g))) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : G ↦
      (0 : GroupHilbert G)) 0)
  exact hs.unique hz

/-- The canonical coefficient functional is a faithful tracial state. -/
def canonicalFaithfulTracialState : FaithfulTracialState (ReducedGroupCStar G) where
  toLinearMap := (canonicalCoefficientAtOne G).toLinearMap
  map_one := by
    change ((1 : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = 1
    simp [deltaOne]
  map_star_mul_self_nonneg T := by
    change 0 ≤ canonicalCoefficientAtOne G (star T * T)
    rw [canonicalCoefficientAtOne_star_mul_self]
    positivity
  map_mul_comm := canonicalCoefficientAtOne_mul_comm G
  eq_zero_of_map_star_mul_self_eq_zero := by
    intro T hT
    change canonicalCoefficientAtOne G (star T * T) = 0 at hT
    rw [canonicalCoefficientAtOne_star_mul_self] at hT
    have hnorm : ‖(T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖ = 0 := by
      have hc : (‖(T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖ : ℂ) = 0 :=
        sq_eq_zero_iff.mp hT
      exact Complex.ofReal_eq_zero.mp hc
    apply eq_zero_of_apply_deltaOne_eq_zero G T
    exact norm_eq_zero.mp hnorm

end

end ReducedGroupCStarTrace

end GroupApproximation
