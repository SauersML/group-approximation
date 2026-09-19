import GroupApproximation.Higman.OmegaTowerConjugateBasisShift

/-!
# The inverse outer Omega shift on conjugate-basis words

This is the negative-sign companion of `OmegaTowerConjugateBasisShift`.
It restricts the iterated inverse shift to `K` and proves naturality on every
free conjugate-basis word.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq

/-- The inverse one-step shift preserves the conjugating subgroup. -/
theorem shiftAutInv_mem_K {x : F₃} (hx : x ∈ K) : shiftAutInv x ∈ K := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with rfl | hx
      · rw [shiftAutInv_b]
        exact K.mul_mem (K.mul_mem c_mem_K b_mem_K) (K.inv_mem c_mem_K)
      · rw [Set.mem_singleton_iff] at hx
        subst x
        rw [shiftAutInv_c]
        exact c_mem_K
  | one => rw [map_one]; exact K.one_mem
  | mul x y _ _ ihx ihy => rw [map_mul]; exact K.mul_mem ihx ihy
  | inv x _ ih => rw [map_inv]; exact K.inv_mem ih

/-- The inverse one-step shift restricted to conjugate-basis indices. -/
def unshiftKHom : ↥K →* ↥K where
  toFun q := ⟨shiftAutInv (q : F₃), shiftAutInv_mem_K q.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _

/-- The recursively iterated inverse shift on conjugate-basis indices. -/
def unshiftKPowHom : ℕ → ↥K →* ↥K
  | 0 => MonoidHom.id ↥K
  | n + 1 => unshiftKHom.comp (unshiftKPowHom n)

theorem unshiftKPowHom_coe (m : ℕ) (q : ↥K) :
    ((unshiftKPowHom m q : ↥K) : F₃) = (shiftAutInv^[m]) (q : F₃) := by
  induction m with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change shiftAutInv (((unshiftKPowHom n q : ↥K) : F₃)) = _
      rw [ih]

theorem shiftAutInv_iterate_a (m : ℕ) : (shiftAutInv^[m]) a = a := by
  induction m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, shiftAutInv_a]

/-- Naturality for one inverse-shift step. -/
theorem shiftAutInv_cbHom (w : FreeGroup ↥K) :
    shiftAutInv (cbHom w) = cbHom (FreeGroup.map unshiftKHom w) := by
  have hhom : shiftAutInv.comp cbHom =
      cbHom.comp (FreeGroup.map unshiftKHom) := by
    refine FreeGroup.ext_hom _ _ fun q => ?_
    simp only [MonoidHom.comp_apply, cbHom_of, FreeGroup.map.of, map_mul, map_inv,
      shiftAutInv_a]
    rfl
  exact DFunLike.congr_fun hhom w

/-- Naturality of the iterated inverse shift on all conjugate-basis words. -/
theorem shiftAutInv_iterate_cbHom (m : ℕ) (w : FreeGroup ↥K) :
    (shiftAutInv^[m]) (cbHom w) =
      cbHom (FreeGroup.map (unshiftKPowHom m) w) := by
  induction m generalizing w with
  | zero => simp [unshiftKPowHom]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [shiftAutInv_cbHom]
      congr 1
      have hcomp :
          (FreeGroup.map unshiftKHom).comp
              (FreeGroup.map (unshiftKPowHom n)) =
            FreeGroup.map (unshiftKPowHom (n + 1)) := by
        refine FreeGroup.ext_hom _ _ fun q => ?_
        simp [unshiftKPowHom]
      exact DFunLike.congr_fun hcomp w

end Omega
end Higman
end GroupApproximation
