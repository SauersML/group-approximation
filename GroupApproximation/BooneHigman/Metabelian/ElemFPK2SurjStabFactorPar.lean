import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, factor step: the parabolic `P` and `(u, t) · padCol c` (bh-met-65c)

Here `R` is an arbitrary unital ring and `P = stab St_n · padCol R^n ⊆ St_{n+1}(R)`.

* `SurjStabFactorInPar y` means `y = stab g · padCol v` for some `g`, `v`.  This set contains
  `1` and is closed under products (`surjStabFactor_inPar_mul`), by the column normal form
  `padCol v · stab h = stab h · padCol (padMat h⁻¹ *ᵥ v)`.
* `(u, t) ᵥ* padMat (padCol c) = (u, t + u ⬝ᵥ c)` (`surjStabFactor_vecMul_padCol`).  So if `u` and
  `c` have disjoint supports, then `padCol c` fixes `(u, 1)`.

Truth check.  `padMat (padCol c) = 1 + (column c in the last column)`.  A row vector `(u, t)`
times it is `(u, t + Σ_p u_p c_p)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `y ∈ P = stab St_n · padCol R^n`. -/
def SurjStabFactorInPar (y : St (n + 1) R) : Prop :=
  ∃ (g : St n R) (v : Fin n → R), y = stab n R g * padCol v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabFactorInPar

theorem surjStabFactor_inPar_of (g : St n R) (v : Fin n → R) :
    SurjStabFactorInPar (stab n R g * padCol v) :=
  ⟨g, v, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_inPar_of

theorem surjStabFactor_inPar_one : SurjStabFactorInPar (1 : St (n + 1) R) :=
  ⟨1, 0, by rw [map_one (stab n R), padCol_zero, one_mul]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_inPar_one

theorem surjStabFactor_inPar_mul {y y' : St (n + 1) R} (hy : SurjStabFactorInPar y)
    (hy' : SurjStabFactorInPar y') : SurjStabFactorInPar (y * y') := by
  obtain ⟨g, v, rfl⟩ := hy
  obtain ⟨h, u, rfl⟩ := hy'
  refine ⟨g * h, padMat h⁻¹ *ᵥ v + u, ?_⟩
  rw [surjStab_mul_swap_mid (surjStab_padCol_mul_stab h v), map_mul (stab n R) g h, padCol_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_inPar_mul

/-- `(u, t) + t' e_{last} = (u, t + t')`. -/
theorem surjStabFactor_vec_add_last (u : Fin n → R) (t s : R) :
    surjStabVec u t + Pi.single (Fin.last n) s = surjStabVec u (t + s) := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · rw [Pi.add_apply, surjStabVec_castSucc, surjStabVec_castSucc,
      Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, add_zero]
  · rw [Pi.add_apply, surjStabVec_last, surjStabVec_last, Pi.single_eq_same]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_vec_add_last

/-- `(u, t) ᵥ* padMat (padCol c) = (u, t + u ⬝ᵥ c)`. -/
theorem surjStabFactor_vecMul_padCol (c u : Fin n → R) (t : R) :
    surjStabVec u t ᵥ* padMat (padCol c) = surjStabVec u (t + u ⬝ᵥ c) := by
  induction c using Pi.single_induction generalizing t with
  | zero => rw [padCol_zero, map_one, Matrix.vecMul_one, dotProduct_zero, add_zero]
  | add f g hf hg =>
    rw [padCol_add, map_mul padMat (padCol f) (padCol g), ← Matrix.vecMul_vecMul, hf t,
      hg (t + u ⬝ᵥ f), dotProduct_add, add_assoc]
  | single p a =>
    rw [padCol_single, padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single,
      surjStabVec_castSucc, dotProduct_single, surjStabFactor_vec_add_last]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_vecMul_padCol

/-- Disjoint supports: `padCol c` fixes `(u, 1)` when `c i = 0 ∨ u i = 0` for all `i`. -/
theorem surjStabFactor_vecMul_padCol_disj (c u : Fin n → R) (h : ∀ i, c i = 0 ∨ u i = 0) :
    surjStabVec u (1 : R) ᵥ* padMat (padCol c) = surjStabVec u 1 := by
  have hd : u ⬝ᵥ c = 0 := by
    show ∑ i, u i * c i = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases h i with hc | hu
    · rw [hc, mul_zero]
    · rw [hu, zero_mul]
  rw [surjStabFactor_vecMul_padCol, hd, add_zero]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabFactor_vecMul_padCol_disj

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
