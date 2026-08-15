import GroupApproximation.Monsters.P13ColumnLift
import GroupApproximation.Monsters.P13ParabolicKernel

/-!
# The transversal factorization of P13

Given the canonical column lift `m` of `P13ColumnLift`, every element
`g` of the presented group factors as the canonical lift of its image
column times an element of the parabolic subgroup — provided the
generator cocycles `sigma (x i c) v` all lie in the parabolic.  That
single membership is the remaining containment step of the
completeness programme and is discharged in the descent files; every
statement here takes it as an explicit hypothesis, so nothing below
asserts it.

The factorization immediately places the kernel of `toSL3` inside the
parabolic subgroup: a kernel element has column `e₃`, whose canonical
lift is trivial.  Combined with the parabolic kernel triviality of
`P13ParabolicKernel`, the kernel is trivial and `toSL3` is injective.
-/

namespace GroupApproximation
namespace P13KernelFactorization

open LiteralP13Presentation P13SteinbergCalculus LiteralP13MatrixModel
open P13ColumnLift P13ParabolicKernel

noncomputable section

/-- The image column of an element: where its matrix sends `e₃`. -/
def col (g : P13) : Fin 3 → ℤ := act (toSL3 g) e3

theorem isColumn_col (g : P13) : IsColumn (col g) := ⟨toSL3 g, rfl⟩

theorem col_one : col 1 = e3 := by
  unfold col
  rw [map_one, act_one]

theorem col_mul (g h : P13) : col (g * h) = act (toSL3 g) (col h) := by
  unfold col
  rw [map_mul, act_mul]

/-- **Transversal factorization.**  If every generator cocycle lies in
the parabolic subgroup, then every element splits as the canonical
lift of its column times a parabolic element. -/
theorem exists_factorization
    (hσ : ∀ (i : Fin 6) (c : ℤ) (v : Fin 3 → ℤ), IsColumn v →
      sigma (x i c) v ∈ Hpar)
    (g : P13) : ∃ h ∈ Hpar, g = m (col g) * h := by
  have hg : g ∈ Subgroup.closure
      (Set.range (PresentedGroup.of (rels := p13Relators))) := by
    rw [PresentedGroup.closure_range_of]
    trivial
  induction hg using Subgroup.closure_induction_left with
  | one =>
      exact ⟨1, Subgroup.one_mem _, by rw [col_one, m_e3, one_mul]⟩
  | mul_left s hs y hy ih =>
      rcases hs with ⟨i, rfl⟩
      obtain ⟨h, hh, hyeq⟩ := ih
      refine ⟨sigma (x i 1) (col y) * h,
        Subgroup.mul_mem _ (hσ i 1 (col y) (isColumn_col y)) hh, ?_⟩
      rw [← x_one i]
      have step1 : x i 1 * y = x i 1 * m (col y) * h := by
        conv_lhs => rw [hyeq]
        group
      calc x i 1 * y = x i 1 * m (col y) * h := step1
        _ = m (act (toSL3 (x i 1)) (col y)) * sigma (x i 1) (col y) * h := by
            rw [mul_m_eq]
        _ = m (col (x i 1 * y)) * (sigma (x i 1) (col y) * h) := by
            rw [col_mul]
            group
  | inv_mul_cancel s hs y hy ih =>
      rcases hs with ⟨i, rfl⟩
      obtain ⟨h, hh, hyeq⟩ := ih
      have hinv : (PresentedGroup.of (rels := p13Relators) i)⁻¹ =
          x i (-1) := by
        rw [← x_one i, ← x_neg]
      rw [hinv]
      refine ⟨sigma (x i (-1)) (col y) * h,
        Subgroup.mul_mem _ (hσ i (-1) (col y) (isColumn_col y)) hh, ?_⟩
      have step1 : x i (-1) * y = x i (-1) * m (col y) * h := by
        conv_lhs => rw [hyeq]
        group
      calc x i (-1) * y = x i (-1) * m (col y) * h := step1
        _ = m (act (toSL3 (x i (-1))) (col y)) *
              sigma (x i (-1)) (col y) * h := by
            rw [mul_m_eq]
        _ = m (col (x i (-1) * y)) * (sigma (x i (-1)) (col y) * h) := by
            rw [col_mul]
            group

/-- **Kernel containment.**  Modulo the generator cocycles, every
kernel element of the matrix model lies in the parabolic subgroup. -/
theorem mem_parabolic_of_map_eq_one
    (hσ : ∀ (i : Fin 6) (c : ℤ) (v : Fin 3 → ℤ), IsColumn v →
      sigma (x i c) v ∈ Hpar)
    {g : P13} (hg : toSL3 g = 1) : g ∈ Hpar := by
  obtain ⟨h, hh, hfac⟩ := exists_factorization hσ g
  have hcol : col g = e3 := by
    unfold col
    rw [hg, act_one]
  rw [hcol, m_e3, one_mul] at hfac
  rwa [hfac]

/-- **Injectivity of the matrix model, modulo the generator
cocycles.**  Combined with the parabolic kernel triviality, the
kernel of `toSL3` is trivial. -/
theorem toSL3_injective
    (hσ : ∀ (i : Fin 6) (c : ℤ) (v : Fin 3 → ℤ), IsColumn v →
      sigma (x i c) v ∈ Hpar) :
    Function.Injective toSL3 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_mem_parabolic_of_map_eq_one
    (mem_parabolic_of_map_eq_one hσ hg) hg

end

end P13KernelFactorization
end GroupApproximation
