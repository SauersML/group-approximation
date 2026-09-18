import GroupApproximation.BooneHigman.Metabelian.SuslinCongPowGen
import GroupApproximation.BooneHigman.Metabelian.SuslinCongDecideWitness
import GroupApproximation.Meta.AxiomGuard

/-!
# The Krstić–McCool-type witnesses lie in `suslinCongPow_gen` and stabilize into `E₃`

Lane `bh-met-92r` (the required sanity test, in Lean).  Over any commutative ring `S`, for all
`t, y : S`, the matrix `[[1 + t y, y³], [t³, 1 - t y + t² y²]]` is obtained from
`σ_Y = E₁₂(y) E₂₁(t) = [[1 + t y, y], [t, 1]]` by two Mennicke steps
(`suslinCongPow_kmShape_mem`):

* `(σ_Y, σ_Y) ↦ [[1 + t y, y²], [-t², 1 - t y]]` (a Cohn-type matrix), then
* `(σ_Y, Cohn) ↦ [[1 + t y, y³], [t³, 1 - t y + t² y²]]`.

Hence `h_{q,k} = suslinCongDecide_km q k ∈ suslinCongPow_gen A[X]` (`t = q`, `y = X^k`),
and the same holds for its image under any `f : A[X] →+* S`, and for the witness
`σ_{q,k} = suslinCongDecide_wit q k`.  With `suslinCongPow_gen_le` these give,
UNCONDITIONALLY, `diag(h_{q,k}, 1) ∈ E₃(A[X])` (`suslinCongPow_stab_km_mem`) and
`diag(f σ_{q,k}, 1) ∈ E₃(S)` (`suslinCongPow_stab_map_wit_mem`).  The explicit factorization
was checked symbolically and numerically in `$SP/bh-met-92r/`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- Congruence for `2 × 2` matrix literals. -/
theorem suslinCongPow_fin2_congr {S : Type*} {a b c d a' b' c' d' : S} (ha : a = a')
    (hb : b = b') (hc : c = c') (hd : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  subst ha hb hc hd
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_fin2_congr

/-- `E₁₂(y) E₂₁(t) = [[1 + t y, y], [t, 1]]`. -/
theorem suslinCongPow_eU_pair_val {S : Type*} [CommRing S] (t y : S) :
    ((elementaryUnit (0 : Fin 2) 1 (by decide) y * elementaryUnit (1 : Fin 2) 0 (by decide) t :
        (Matrix (Fin 2) (Fin 2) S)ˣ) : Matrix (Fin 2) (Fin 2) S) = !![1 + t * y, y; t, 1] := by
  rw [Units.val_mul, suslinCongPow_eU_val, suslinCongPow_eU_val]
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] <;> ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_eU_pair_val

/-- **Two Mennicke steps**: every Mennicke-closed subgroup of `GL₂(S)` containing `E₂(S)`
contains every `u = [[1 + t y, y³], [t³, 1 - t y + t² y²]]`. -/
theorem suslinCongPow_kmShape_mem {S : Type*} [CommRing S]
    (H : Subgroup (Matrix (Fin 2) (Fin 2) S)ˣ) (hE : elementaryGroup (Fin 2) S ≤ H)
    (hM : suslinCongPow_MennickeClosed H) (t y : S) (u : (Matrix (Fin 2) (Fin 2) S)ˣ)
    (hu : (u : Matrix (Fin 2) (Fin 2) S) =
      !![1 + t * y, y ^ 3; t ^ 3, 1 - t * y + t ^ 2 * y ^ 2]) :
    u ∈ H := by
  have hY : elementaryUnit (0 : Fin 2) 1 (by decide) y *
      elementaryUnit (1 : Fin 2) 0 (by decide) t ∈ H :=
    mul_mem (hE (elementaryUnit_mem _ _ _ _)) (hE (elementaryUnit_mem _ _ _ _))
  have hdet : Matrix.det !![1 + t * y, y * y; -(t * t), 1 - t * 1 * y] = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  obtain ⟨c, hc⟩ : ∃ c : (Matrix (Fin 2) (Fin 2) S)ˣ,
      (c : Matrix (Fin 2) (Fin 2) S) = !![1 + t * y, y * y; -(t * t), 1 - t * 1 * y] :=
    ⟨Matrix.SpecialLinearGroup.toGL ⟨_, hdet⟩, rfl⟩
  have h1 : (1 + t * y) * 1 - y * t = 1 := by ring
  have hcH : c ∈ H :=
    hM _ _ c (1 + t * y) y t 1 y t 1 h1 (suslinCongPow_eU_pair_val t y)
      (suslinCongPow_eU_pair_val t y) hc hY hY
  refine hM _ c u (1 + t * y) y t 1 (y * y) (-(t * t)) (1 - t * 1 * y) h1
    (suslinCongPow_eU_pair_val t y) hc ?_ hY hcH
  exact hu.trans (suslinCongPow_fin2_congr (by ring) (by ring) (by ring) (by ring))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_kmShape_mem

/-- `E₂(S) ≤ suslinCongPow_gen S`. -/
theorem suslinCongPow_elementary_le_gen (S : Type*) [CommRing S] :
    elementaryGroup (Fin 2) S ≤ suslinCongPow_gen S :=
  fun _ hσ ↦ suslinCongPow_mem_gen_of fun _ hE _ ↦ hE hσ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_elementary_le_gen

/-- **`h_{q,k} ∈ suslinCongPow_gen A[X]`.** -/
theorem suslinCongPow_km_mem {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    suslinCongDecide_km q k ∈ suslinCongPow_gen A[X] :=
  suslinCongPow_mem_gen_of fun H hE hM ↦
    suslinCongPow_kmShape_mem H hE hM (C q) (X ^ k) _ rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_km_mem

/-- **`diag(h_{q,k}, 1) ∈ E₃(A[X])`**, unconditionally. -/
theorem suslinCongPow_stab_km_mem {A : Type*} [CommRing A] (q : A) (k : ℕ) :
    stabilizeUnit (R := A[X]) (κ := Unit) (suslinCongDecide_km q k) ∈
      elementaryGroup (Fin 2 ⊕ Unit) A[X] :=
  suslinCongPow_gen_le A[X] (suslinCongPow_km_mem q k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinCongPow_stab_km_mem

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
