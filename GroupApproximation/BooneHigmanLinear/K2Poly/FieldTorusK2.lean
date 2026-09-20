import GroupApproximation.BooneHigmanLinear.K2Poly.FieldTorus
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Diagonal
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols over a field lie in `K₂`, so the torus defect lands in `Z`

k2-poly piece A5.2 (lane k2-field-b). In the residual `FieldStabAt F` (K2Poly/FieldNagao), the
symbol factors that Euclid's algorithm produces over an arbitrary field must land in
`Z = C(K₂(I, F))`. This file proves that.

* `projection_h_mul`: in `E_I(F)`, `h_ij(u v) ↦ h_ij(u) h_ij(v)`, since the image is
  `diag(u at i, u⁻¹ at j, 1 elsewhere)` (`manuscriptSentence_projectionDiagonalElement`) and
  diagonal matrices multiply entrywise over a commutative ring.
* `symbol_mem_K2`: `symbol_ij(u, v) = h(u v) h(u)⁻¹ h(v)⁻¹ ∈ K₂(I, F)`.
* `constSymbol_mem_constK2`: `C(symbol) ∈ C(K₂(I, F))`, i.e. in `fnZ F`.
* `fieldTorus_mul_mem`: `t(c c') = z · t(c') · t(c)` with `z ∈ C(K₂(I, F))`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.Metabelian.ElemFP
open GroupApproximation.BooneHigman.SteinbergBasic (K2 mem_K2_iff)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h
  manuscriptSentence_projectionDiagonalElement)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- The projection is multiplicative on each torus over a field. -/
theorem projection_h_mul (i j : I) (hij : i ≠ j) (u v : Fˣ) :
    projection (h i j hij (u * v)) = projection (h i j hij u) * projection (h i j hij v) := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, manuscriptSentence_projectionDiagonalElement,
    manuscriptSentence_projectionDiagonalElement, manuscriptSentence_projectionDiagonalElement,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp
  ring

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.projection_h_mul

/-- **Symbols over a field lie in `K₂`.** -/
theorem symbol_mem_K2 (i j : I) (hij : i ≠ j) (u v : Fˣ) :
    FieldK2.symbol i j hij u v ∈ K2 I F := by
  have hc : projection (h i j hij u) * projection (h i j hij v) =
      projection (h i j hij v) * projection (h i j hij u) := by
    rw [← projection_h_mul, ← projection_h_mul, mul_comm u v]
  rw [mem_K2_iff, FieldK2.symbol, map_mul, map_mul, map_inv, map_inv, projection_h_mul, hc]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.symbol_mem_K2

/-- A constant symbol lies in the constant `K₂`, `Z = C(K₂(I, F))` (the subgroup `fnZ F`). -/
theorem constSymbol_mem_constK2 (i j : I) (hij : i ≠ j) (u v : Fˣ) :
    ringMap (I := I) (Polynomial.C : F →+* Polynomial F) (FieldK2.symbol i j hij u v) ∈
      (K2 I F).map (ringMap (I := I) (Polynomial.C : F →+* Polynomial F)) :=
  Subgroup.mem_map_of_mem _ (symbol_mem_K2 i j hij u v)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.constSymbol_mem_constK2

/-- **The torus defect lies in `Z`.** `t(c c') = z · t(c') · t(c)` with `z ∈ C(K₂(I, F))`. -/
theorem fieldTorus_mul_mem (m L : I) (hmL : m ≠ L) (c c' : Fˣ) :
    ∃ z ∈ (K2 I F).map (ringMap (I := I) (Polynomial.C : F →+* Polynomial F)),
      fieldTorus F m L hmL (c * c') = z * fieldTorus F m L hmL c' * fieldTorus F m L hmL c :=
  ⟨_, constSymbol_mem_constK2 m L hmL c c', fieldTorus_mul m L hmL c c'⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldTorus_mul_mem

end GroupApproximation.BooneHigmanLinear.K2Poly
