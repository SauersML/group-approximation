import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.LiteralBaseTranslationNormal

/-!
# The literal translation subgroup is the full integral lattice

The three commuting translation letters define a homomorphism from `ℤ³` to
the literal base.  The exact affine matrix quotient detects its three
coordinates entry by entry, so this homomorphism is injective.  Its range is
the translation subgroup by construction.

This argument is independent of completeness of the eight rotation
relations: it uses the matrix model only to separate translation words.
-/

namespace GroupApproximation
namespace LiteralBaseTranslationLattice

open ExplicitLinearModel LiteralNonMFLinearWitness
open LiteralBaseRelations LiteralBaseTranslationNormal

noncomputable section

abbrev Lattice := Fin 3 → ℤ

private def tv1 : translations := ⟨v1, v1_mem_translations⟩
private def tv2 : translations := ⟨v2, v2_mem_translations⟩
private def tv3 : translations := ⟨v3, v3_mem_translations⟩

local instance translationsCommGroup : CommGroup translations :=
  { (inferInstance : Group translations) with
    mul_comm := fun a b => Subtype.ext (translations_commute a.property b.property).eq }

/-- Evaluation of an exponent vector in the three commuting literal
translations, with codomain restricted to the translation subgroup. -/
def latticeToTranslations : Multiplicative Lattice →* translations where
  toFun a := tv1 ^ a.toAdd 0 * tv2 ^ a.toAdd 1 * tv3 ^ a.toAdd 2
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add]
    ac_rfl

/-- Evaluation of a lattice vector in the full literal base. -/
def latticeToBase : Multiplicative Lattice →* LiteralNonMFPresentation.Base :=
  translations.subtype.comp latticeToTranslations

@[simp] theorem latticeToBase_basis_zero :
    latticeToBase (Multiplicative.ofAdd (Pi.single 0 1)) = v1 := by
  simp [latticeToBase, latticeToTranslations, tv1, tv2, tv3]

@[simp] theorem latticeToBase_basis_one :
    latticeToBase (Multiplicative.ofAdd (Pi.single 1 1)) = v2 := by
  simp [latticeToBase, latticeToTranslations, tv1, tv2, tv3]

@[simp] theorem latticeToBase_basis_two :
    latticeToBase (Multiplicative.ofAdd (Pi.single 2 1)) = v3 := by
  simp [latticeToBase, latticeToTranslations, tv1, tv2, tv3]

/-! ## Exact affine translation matrices -/

def translationMatrix (a : Lattice) : Mat :=
  !![1, 0, 0, a 0; 0, 1, 0, a 1; 0, 0, 1, a 2; 0, 0, 0, 1]

theorem translationMatrix_add (a b : Lattice) :
    translationMatrix (a + b) = translationMatrix a * translationMatrix b := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [translationMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem translationMatrix_neg (a : Lattice) :
    translationMatrix a * translationMatrix (-a) = 1 := by
  rw [← translationMatrix_add]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [translationMatrix]

theorem translationMatrix_neg' (a : Lattice) :
    translationMatrix (-a) * translationMatrix a = 1 := by
  rw [← translationMatrix_add]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [translationMatrix]

def translationUnit (a : Lattice) : Matˣ :=
  ⟨translationMatrix a, translationMatrix (-a),
    translationMatrix_neg a, translationMatrix_neg' a⟩

def latticeMatrixHom : Multiplicative Lattice →* Matˣ where
  toFun a := translationUnit a.toAdd
  map_one' := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [translationUnit, translationMatrix]
  map_mul' a b := Units.ext (translationMatrix_add a.toAdd b.toAdd)

@[simp] theorem latticeMatrixHom_basis_zero :
    latticeMatrixHom (Multiplicative.ofAdd (Pi.single 0 1)) = v1U := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [latticeMatrixHom, translationUnit, translationMatrix, v1U, v1M,
      Pi.single_apply]
  all_goals decide

@[simp] theorem latticeMatrixHom_basis_one :
    latticeMatrixHom (Multiplicative.ofAdd (Pi.single 1 1)) = v2U := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [latticeMatrixHom, translationUnit, translationMatrix, v2U, v2M,
      Pi.single_apply]
  all_goals decide

@[simp] theorem latticeMatrixHom_basis_two :
    latticeMatrixHom (Multiplicative.ofAdd (Pi.single 2 1)) = v3U := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [latticeMatrixHom, translationUnit, translationMatrix, v3U, v3M,
      Pi.single_apply]
  all_goals decide

theorem lattice_eq_basis_product (a : Multiplicative Lattice) :
    a = Multiplicative.ofAdd (Pi.single 0 1) ^ a.toAdd 0 *
      Multiplicative.ofAdd (Pi.single 1 1) ^ a.toAdd 1 *
      Multiplicative.ofAdd (Pi.single 2 1) ^ a.toAdd 2 := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> simp

/-- The range of lattice evaluation is exactly the subgroup generated by the
three translation letters. -/
theorem latticeToBase_range : latticeToBase.range = translations := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rcases hg with ⟨a, rfl⟩
    exact (latticeToTranslations a).property
  · change Subgroup.closure ({v1, v2, v3} : Set LiteralNonMFPresentation.Base) ≤
      latticeToBase.range
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd (Pi.single 0 1), latticeToBase_basis_zero⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 1 1), latticeToBase_basis_one⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 2 1), latticeToBase_basis_two⟩

end

end LiteralBaseTranslationLattice
end GroupApproximation
