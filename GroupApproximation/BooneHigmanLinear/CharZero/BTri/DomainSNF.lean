import GroupApproximation.BooneHigmanLinear.CharZero.BTri.DomainType
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Adjugate
import GroupApproximation.Meta.AxiomGuard

/-!
# Z.3, part 4: Smith normal form of `3 × 3` matrices over a principal ideal domain

Lane `fix-bh-a`, piece Z.3 (board `k2-poly.md`).  This file is the linear-algebra input for the
edge and chamber normal forms and for the Cartan decomposition (k2-bt-sc's Z.4 needs).

* `colSpan X`: the `A`-span of the columns of `X`.
* `exists_eq_mul_of_colSpan_le`: `colSpan Y ≤ colSpan X → ∃ W, Y = X W`.
* `exists_gl_of_colSpan_eq`: for `det X ≠ 0`, equal column spans give `Y = X V`, `V ∈ GL₃(A)`.
* **`exists_snf`** (from Mathlib's `Submodule.exists_smith_normal_form_of_rank_eq`): for
  `det K ≠ 0`, `K = U · diag(a) · V` with `U, V ∈ GL₃(A)`.
* **`exists_snf_pow`**: if moreover `det K ∣ p^n` for a prime `p`, then the diagonal can be taken
  as `diag(p^{e₀}, p^{e₁}, p^{e₂})`: the units of the `aᵢ ~ p^{eᵢ}` are absorbed into `V`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open Matrix

section SNF

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The `A`-span of the columns of `X`. -/
def colSpan (X : Matrix (Fin 3) (Fin 3) A) : Submodule A (Fin 3 → A) :=
  Submodule.span A (Set.range fun j : Fin 3 => fun i : Fin 3 => X i j)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.colSpan

theorem col_mem_colSpan (X : Matrix (Fin 3) (Fin 3) A) (j : Fin 3) :
    (fun i => X i j) ∈ colSpan X :=
  Submodule.subset_span ⟨j, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.col_mem_colSpan

theorem exists_eq_mul_of_colSpan_le {X Y : Matrix (Fin 3) (Fin 3) A}
    (h : colSpan Y ≤ colSpan X) : ∃ W : Matrix (Fin 3) (Fin 3) A, Y = X * W := by
  have hj : ∀ j : Fin 3, ∃ c : Fin 3 → A, ∑ l, c l • (fun i => X i l) = fun i => Y i j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun A).mp (h (col_mem_colSpan Y j))
  choose c hc using hj
  refine ⟨Matrix.of fun l j => c j l, ?_⟩
  ext i j
  have hij := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hij
  rw [← hij, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.of_apply]
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_eq_mul_of_colSpan_le

theorem colSpan_mul_le (X W : Matrix (Fin 3) (Fin 3) A) : colSpan (X * W) ≤ colSpan X := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  have e : (fun i => (X * W) i j) = ∑ l, W l j • fun i => X i l := by
    ext i
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (col_mem_colSpan X l)

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.colSpan_mul_le

/-- Cancellation: `X W = X` with `det X ≠ 0` gives `W = 1`. -/
theorem eq_one_of_mul_eq_self {X W : Matrix (Fin 3) (Fin 3) A} (hX : X.det ≠ 0)
    (h : X * W = X) : W = 1 := by
  have e : X.det • W = X.det • (1 : Matrix (Fin 3) (Fin 3) A) := by
    calc X.det • W = (X.adjugate * X) * W := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
      _ = X.adjugate * (X * W) := by rw [mul_assoc]
      _ = X.adjugate * X := by rw [h]
      _ = X.det • (1 : Matrix (Fin 3) (Fin 3) A) := Matrix.adjugate_mul X
  ext i j
  have := congrFun (congrFun e i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hX this

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.eq_one_of_mul_eq_self

/-- **Equal column spans**: for `det X ≠ 0`, `colSpan X = colSpan Y` gives `Y = X V` with
`V ∈ GL₃(A)`. -/
theorem exists_gl_of_colSpan_eq {X Y : Matrix (Fin 3) (Fin 3) A} (hX : X.det ≠ 0)
    (e : colSpan X = colSpan Y) : ∃ V : GL (Fin 3) A, Y = X * (V : Matrix (Fin 3) (Fin 3) A) := by
  obtain ⟨W₁, h₁⟩ := exists_eq_mul_of_colSpan_le e.symm.le
  obtain ⟨W₂, h₂⟩ := exists_eq_mul_of_colSpan_le e.le
  have h12 : W₁ * W₂ = 1 := eq_one_of_mul_eq_self hX (by rw [← mul_assoc, ← h₁, ← h₂])
  exact ⟨⟨W₁, W₂, h12, mul_eq_one_comm.mp h12⟩, h₁⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_gl_of_colSpan_eq

variable [IsPrincipalIdealRing A]

/-- **Smith normal form** of a `3 × 3` matrix with nonzero determinant over a PID. -/
theorem exists_snf (K : Matrix (Fin 3) (Fin 3) A) (hK : K.det ≠ 0) :
    ∃ (U V : GL (Fin 3) A) (a : Fin 3 → A),
      K = (U : Matrix (Fin 3) (Fin 3) A) * diagonal a * (V : Matrix (Fin 3) (Fin 3) A) := by
  classical
  let b := Pi.basisFun A (Fin 3)
  have hli : LinearIndependent A (fun j : Fin 3 => fun i : Fin 3 => K i j) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hK
  have hrank : Module.finrank A (colSpan K) = Module.finrank A (Fin 3 → A) := by
    rw [Module.finrank_fin_fun]
    exact (finrank_span_eq_card hli).trans (Fintype.card_fin 3)
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b hrank
  letI : Invertible (b.toMatrix b') := b.invertibleToMatrix b'
  let U : GL (Fin 3) A := unitOfInvertible (b.toMatrix b')
  have hU : ∀ i j, (U : Matrix (Fin 3) (Fin 3) A) i j = b' j i := fun i j => by
    change b.toMatrix b' i j = _
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hcol : (fun j : Fin 3 => fun i : Fin 3 => ((U : Matrix (Fin 3) (Fin 3) A) * diagonal a) i j) =
      fun j => ((ab' j : colSpan K) : Fin 3 → A) := by
    funext j i
    rw [Matrix.mul_diagonal, hU, hab j, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hspan : colSpan ((U : Matrix (Fin 3) (Fin 3) A) * diagonal a) = colSpan K := by
    have hr : (Set.range fun j : Fin 3 => ((ab' j : colSpan K) : Fin 3 → A)) =
        (colSpan K).subtype '' Set.range ab' := by
      rw [← Set.range_comp]
      rfl
    rw [colSpan, hcol, hr, ← Submodule.map_span, ab'.span_eq, Submodule.map_subtype_top]
  obtain ⟨V, hV⟩ := exists_gl_of_colSpan_eq hK hspan.symm
  refine ⟨U, V⁻¹, a, ?_⟩
  rw [hV, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_snf

/-- The diagonal unit `diag(w₀, w₁, w₂)` of `GL₃(A)`. -/
def diagUnit (w : Fin 3 → Aˣ) : GL (Fin 3) A where
  val := diagonal fun i => (w i : A)
  inv := diagonal fun i => ((w i)⁻¹ : Aˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.diagUnit

/-- **Smith normal form with `p`-power diagonal**: if `det K ∣ p^n` for a prime `p`, then
`K = U · diag(p^{e₀}, p^{e₁}, p^{e₂}) · V` with `U, V ∈ GL₃(A)`. -/
theorem exists_snf_pow {p : A} (hp : Prime p) (K : Matrix (Fin 3) (Fin 3) A) {n : ℕ}
    (hK : K.det ∣ p ^ n) :
    ∃ (U V : GL (Fin 3) A) (e : Fin 3 → ℕ),
      K = (U : Matrix (Fin 3) (Fin 3) A) * diagonal (fun i => p ^ e i) *
        (V : Matrix (Fin 3) (Fin 3) A) := by
  have hK0 : K.det ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff] at hK
    exact pow_ne_zero n hp.ne_zero hK
  obtain ⟨U, V, a, hUV⟩ := exists_snf K hK0
  -- each `a i` divides `det K`, hence a power of `p`
  have hdet : K.det = (U : Matrix (Fin 3) (Fin 3) A).det * (∏ i, a i) *
      (V : Matrix (Fin 3) (Fin 3) A).det := by
    rw [hUV, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hdvd : ∀ i, a i ∣ p ^ n := fun i => by
    refine dvd_trans ?_ hK
    rw [hdet]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) _) _
  have hpow : ∀ i, ∃ (e : ℕ) (w : Aˣ), a i * w = p ^ e := fun i => by
    obtain ⟨e, -, w, hw⟩ := (dvd_prime_pow hp n).mp (hdvd i)
    exact ⟨e, w, hw⟩
  choose e w hw using hpow
  have hdiag : diagonal a = diagonal (fun i => p ^ e i) *
      ((diagUnit fun i => (w i)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) := by
    change diagonal a = diagonal (fun i => p ^ e i) * diagonal (fun i => (((w i)⁻¹ : Aˣ) : A))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← hw i, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨U, diagUnit (fun i => (w i)⁻¹) * V, e, ?_⟩
  rw [hUV, hdiag, Units.val_mul]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigmanLinear.BTri.exists_snf_pow

end SNF

end BTri
end BooneHigmanLinear
end GroupApproximation
