import GroupApproximation.Higman.OmegaTowerShiftSeam

/-!
# The outer Omega shift on arbitrary conjugate-basis words

The pinch classifier returns a word in the free conjugate basis, not merely a
single sequence letter.  This file lifts the `m`-fold shift to the basis index
subgroup `K = ⟨b,c⟩` and proves naturality of `cbHom` for every such word.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open Conj Seq

/-- The one-step shift preserves the conjugating subgroup. -/
theorem shiftAut_mem_K {x : F₃} (hx : x ∈ K) : shiftAut x ∈ K := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with rfl | hx
      · rw [shiftAut_b]
        exact K.mul_mem (K.mul_mem (K.inv_mem c_mem_K) b_mem_K) c_mem_K
      · rw [Set.mem_singleton_iff] at hx
        subst x
        rw [shiftAut_c]
        exact c_mem_K
  | one => rw [map_one]; exact K.one_mem
  | mul x y _ _ ihx ihy => rw [map_mul]; exact K.mul_mem ihx ihy
  | inv x _ ih => rw [map_inv]; exact K.inv_mem ih

/-- Every positive power of the shift preserves `K`. -/
theorem shiftEquiv_pow_mem_K (m : ℕ) {x : F₃} (hx : x ∈ K) :
    ((shiftEquiv : MulAut F₃) ^ m) x ∈ K := by
  induction m generalizing x with
  | zero => simpa using hx
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply]
      exact ih (shiftAut_mem_K hx)

/-- The `m`-fold shift restricted to the conjugate-basis index subgroup. -/
def shiftKPowHom (m : ℕ) : ↥K →* ↥K where
  toFun q := ⟨((shiftEquiv : MulAut F₃) ^ m) (q : F₃),
    shiftEquiv_pow_mem_K m q.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul _ _ _

theorem shiftEquiv_pow_a (m : ℕ) :
    ((shiftEquiv : MulAut F₃) ^ m) a = a := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, MulAut.mul_apply]
      change ((shiftEquiv : MulAut F₃) ^ n) (shiftAut a) = a
      rw [shiftAut_a, ih]

/-- **Naturality on the whole free conjugate basis.** -/
theorem shiftEquiv_pow_cbHom (m : ℕ) (w : FreeGroup ↥K) :
    ((shiftEquiv : MulAut F₃) ^ m) (cbHom w) =
      cbHom (FreeGroup.map (shiftKPowHom m) w) := by
  have hhom :
      ((shiftEquiv : MulAut F₃) ^ m).toMonoidHom.comp cbHom =
        cbHom.comp (FreeGroup.map (shiftKPowHom m)) := by
    refine FreeGroup.ext_hom _ _ fun q => ?_
    simp only [MonoidHom.comp_apply, cbHom_of, FreeGroup.map.of, map_mul, map_inv]
    rw [show (((shiftEquiv : MulAut F₃) ^ m).toMonoidHom a) = a by
      exact shiftEquiv_pow_a m]
    rfl
  exact DFunLike.congr_fun hhom w

end Omega
end Higman
end GroupApproximation
