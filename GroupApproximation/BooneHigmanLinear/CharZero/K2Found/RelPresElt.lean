import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.RelPresAdj
import GroupApproximation.Meta.AxiomGuard

/-!
# The canonical map `St(A, 𝔄) → St(A)` from van der Kallen's elements (k2-poly, F.2/F.3)

Given `hX : VdK.Elements I A` (piece F.1, lane k2-vdk), `X_{v,w} ↦ X(v, w)` respects Tulenbaev's
relations (`can`). Relations (1.1) and (1.2) are `hX.mul` and `hX.conj`; (1.3) follows from them
by Tulenbaev's commutator argument (`elt_frame`). `elt_conj` is the conjugation formula
`y X(v, w) y⁻¹ = X(π(y) v, w π(y)⁻¹)` in `St(A)`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace RelPres

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (conjPair stdPair U Elements)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

section Elt

variable (hX : Elements I A)

theorem elt_congr {p q : (I → A) × (I → A)} (h : p = q) (hp : p ∈ U I A) (hq : q ∈ U I A) :
    hX.elt p hp = hX.elt q hq := by
  subst h
  rfl

theorem elt_zero (v : I → A) (h : (v, (0 : I → A)) ∈ U I A) : hX.elt (v, 0) h = 1 := by
  have h0 : hX.elt (v, 0) h * hX.elt (v, 0) h = hX.elt (v, 0) h := by
    rw [hX.mul v 0 0 h h (VdK.add_mem h h)]
    exact elt_congr hX (by simp) _ _
  exact mul_left_cancel (h0.trans (mul_one _).symm)

#audit_axioms elt_zero

theorem elt_neg (v w : I → A) (h : (v, w) ∈ U I A) (h' : (v, -w) ∈ U I A) :
    hX.elt (v, -w) h' = (hX.elt (v, w) h)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [hX.mul v w (-w) h h' (VdK.add_mem h h'),
    elt_congr hX (show (v, w + -w) = (v, (0 : I → A)) by simp) _ (VdK.zero_mem h)]
  exact elt_zero hX v _

#audit_axioms elt_neg

/-- Tulenbaev's (1.3) from vdK's two relations, via `⁅X(v, b u), X(v', w)⁆`. -/
theorem elt_frame (v v' w u : I → A) (b : A) (hu : u ⬝ᵥ v = 0) (hu' : u ⬝ᵥ v' = 1)
    (hw : w ⬝ᵥ v = 0) (hv : VdK.IsUnimodular v) (h₁ : (b • v + v', w) ∈ U I A)
    (h₂ : (v, b • w) ∈ U I A) (h₃ : (v', w) ∈ U I A) :
    hX.elt (b • v + v', w) h₁ = hX.elt (v, b • w) h₂ * hX.elt (v', w) h₃ := by
  have hP : (v, b • u) ∈ U I A :=
    VdK.mem_U.2 ⟨hv, by rw [smul_dotProduct, hu, smul_zero]⟩
  have hPn : (v, -(b • u)) ∈ U I A := VdK.neg_mem hP
  have hwv' : w ⬝ᵥ v' = 0 := (VdK.mk_mem_U.1 h₃).2
  have e1 : hX.elt (v, b • u) hP * hX.elt (v', w) h₃ * (hX.elt (v, b • u) hP)⁻¹ =
      hX.elt (b • v + v', w) h₁ := by
    rw [hX.conj]
    refine elt_congr hX (Prod.ext ?_ ?_) _ _
    · change v' + ((b • u) ⬝ᵥ v') • v = b • v + v'
      rw [smul_dotProduct, hu', smul_eq_mul, mul_one, add_comm]
    · change w - (w ⬝ᵥ v) • (b • u) = w
      rw [hw, zero_smul, sub_zero]
  have hsum : (v, -(b • u) + b • w) ∈ U I A := VdK.add_mem hPn h₂
  have e2 : hX.elt (v', w) h₃ * hX.elt (v, -(b • u)) hPn * (hX.elt (v', w) h₃)⁻¹ =
      hX.elt (v, -(b • u) + b • w) hsum := by
    rw [hX.conj]
    refine elt_congr hX (Prod.ext ?_ ?_) _ _
    · change v + (w ⬝ᵥ v) • v' = v
      rw [hw, zero_smul, add_zero]
    · change -(b • u) - ((-(b • u)) ⬝ᵥ v') • w = -(b • u) + b • w
      rw [neg_dotProduct, smul_dotProduct, hu', smul_eq_mul, mul_one, neg_smul, sub_neg_eq_add]
  have e3 : hX.elt (v, -(b • u)) hPn = (hX.elt (v, b • u) hP)⁻¹ := elt_neg hX v (b • u) hP hPn
  rw [e3] at e2
  have e4 : hX.elt (v, b • u) hP * hX.elt (v, -(b • u) + b • w) hsum = hX.elt (v, b • w) h₂ := by
    rw [hX.mul v (b • u) (-(b • u) + b • w) hP hsum (VdK.add_mem hP hsum)]
    exact elt_congr hX (by simp) _ _
  rw [← e1, ← e4, ← e2]
  group

#audit_axioms elt_frame

theorem smulPair_mem_U (g : (Matrix I I A)ˣ) {p : (I → A) × (I → A)} (hp : p ∈ U I A) :
    smulPair g p ∈ U I A := by
  obtain ⟨⟨k, hk⟩, hwv⟩ := VdK.mem_U.1 hp
  refine VdK.mem_U.2 ⟨⟨k ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A), ?_⟩, ?_⟩
  · change (k ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((g : Matrix I I A) *ᵥ p.1) = 1
    rw [smulPair_dot, hk]
  · change (p.2 ᵥ* ((g⁻¹ : (Matrix I I A)ˣ) : Matrix I I A)) ⬝ᵥ ((g : Matrix I I A) *ᵥ p.1) = 0
    rw [smulPair_dot, hwv]

#audit_axioms smulPair_mem_U

/-- **Conjugation of vdK elements**: `y X(v, w) y⁻¹ = X(π(y) v, w π(y)⁻¹)`. -/
theorem elt_conj (y : SteinbergGroup I A) (p : (I → A) × (I → A)) (hp : p ∈ U I A) :
    y * hX.elt p hp * y⁻¹ =
      hX.elt (smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) p)
        (smulPair_mem_U _ hp) := by
  let S : Subgroup (SteinbergGroup I A) :=
    { carrier := {y | ∀ p (hp : p ∈ U I A), y * hX.elt p hp * y⁻¹ =
        hX.elt (smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) p)
          (smulPair_mem_U _ hp)}
      one_mem' := fun p hp => by
        rw [one_mul, inv_one, mul_one]
        exact elt_congr hX (by rw [map_one]; exact (smulPair_one p).symm) _ _
      mul_mem' := fun {y z} hy hz p hp => by
        rw [mul_inv_rev, show y * z * hX.elt p hp * (z⁻¹ * y⁻¹) =
          y * (z * hX.elt p hp * z⁻¹) * y⁻¹ by group, hz, hy]
        exact elt_congr hX (by rw [map_mul, Subgroup.coe_mul, smulPair_mul]) _ _
      inv_mem' := fun {y} hy p hp => by
        have h := hy (smulPair ((projection y⁻¹ : elementaryGroup I A) : (Matrix I I A)ˣ) p)
          (smulPair_mem_U _ hp)
        rw [elt_congr hX (show smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ)
          (smulPair ((projection y⁻¹ : elementaryGroup I A) : (Matrix I I A)ˣ) p) = p by
            rw [← smulPair_mul, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
              Subgroup.coe_one, smulPair_one]) _ hp] at h
        rw [← h]
        group }
  have hy : y ∈ S := by
    refine PresentedGroup.generated_by _ S ?_ y
    rintro ⟨i, j, hij, t⟩
    show ∀ p (hp : p ∈ U I A), _
    intro p hp
    change x i j hij t * hX.elt p hp * (x i j hij t)⁻¹ =
      hX.elt (smulPair ((projection (x i j hij t) : elementaryGroup I A) : (Matrix I I A)ˣ) p)
        (smulPair_mem_U _ hp)
    rw [projection_x, ← hX.std i j hij t, hX.conj]
    exact elt_congr hX (smulPair_elementaryUnit hij t p).symm _ _
  exact (show ∀ p (hp : p ∈ U I A), y * hX.elt p hp * y⁻¹ =
    hX.elt (smulPair ((projection y : elementaryGroup I A) : (Matrix I I A)ˣ) p)
      (smulPair_mem_U _ hp) from hy) p hp

#audit_axioms elt_conj

variable (𝔄 : Ideal A)

/-- **The canonical map** `St(A, 𝔄) →* St(A)`, `X_{v,w} ↦ X(v, w)`. -/
noncomputable def can : RelSt I A 𝔄 →* SteinbergGroup I A :=
  PresentedGroup.toGroup (f := fun p : RGen I A 𝔄 => hX.elt p.1 p.2.mem_U) (by
    intro r hr
    change IsRel 𝔄 r at hr
    cases hr with
    | add v w w' h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        exact hX.mul v w w' h₁.mem_U h₂.mem_U h₃.mem_U
    | conj p q hp hq hc =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        exact hX.conj p q hp.mem_U hq.mem_U
    | frame v v' w u b hu hu' hw h₁ h₂ h₃ =>
        simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
        rw [mul_inv_eq_one]
        exact elt_frame hX v v' w u b hu hu' hw h₂.1.isUnimodular h₁.mem_U h₂.mem_U h₃.mem_U)

theorem can_X (p : (I → A) × (I → A)) (hp : RMem 𝔄 p) : can hX 𝔄 (X p hp) = hX.elt p hp.mem_U :=
  PresentedGroup.toGroup.of _

#audit_axioms can_X

end Elt

end RelPres
end K2Found
end BooneHigmanLinear
end GroupApproximation
