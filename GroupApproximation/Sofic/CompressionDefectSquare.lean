import GroupApproximation.Sofic.MarkedCompressionInclusionData
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The marked compression word as a squared defect

For the commutator convention `[x,y] = x y x⁻¹ y⁻¹`, conjugating an
involution `d` by `a` gives the elementary identity

`[d, a d a⁻¹] = [d,a]²`.

Applied to `d = t c t⁻¹`, this places the marked compression word in the
normal closure of the pointwise compression defects `[d, ι(γ)]`.  The
involution hypothesis on `c` is explicit because
`MarkedCompressionInclusionData` deliberately records only the analytic data
and does not require `c` itself to have order two.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u

/-- If `d` is an involution, its commutator with its `a`-conjugate is the
square of the pointwise defect `[d,a]`.  This is the group identity used by
the manuscript's `lem:square`. -/
theorem commutator_conjugate_eq_commutator_sq_of_sq_eq_one
    {G : Type*} [Group G] (d a : G) (hd : d ^ 2 = 1) :
    ⁅d, a * d * a⁻¹⁆ = ⁅d, a⁆ ^ 2 := by
  have hd_inv : d⁻¹ = d := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hd
  simp only [commutatorElement_def, _root_.mul_inv_rev, inv_inv, hd_inv,
    pow_two]
  group

namespace MarkedCompressionInclusionData

variable {Gamma : Type} {E : Type u} [Group Gamma] [Group E]

/-- The pointwise defects associated to marked-compression inclusion data. -/
def compressionDefectSet (D : MarkedCompressionInclusionData Gamma E) : Set E :=
  Set.range fun gamma : Gamma ↦
    ⁅D.t * D.c * D.t⁻¹, D.iota gamma⁆

/-- The normal closure of the pointwise compression defects. -/
def compressionDefectNormal
    (D : MarkedCompressionInclusionData Gamma E) : Subgroup E :=
  Subgroup.normalClosure D.compressionDefectSet

/-- Conjugating an involution preserves its square relation. -/
theorem transported_sq_eq_one (D : MarkedCompressionInclusionData Gamma E)
    (hc : D.c ^ 2 = 1) :
    (D.t * D.c * D.t⁻¹) ^ 2 = 1 := by
  calc
    (D.t * D.c * D.t⁻¹) ^ 2 = D.t * D.c ^ 2 * D.t⁻¹ := by
      simp only [pow_two]
      group
    _ = 1 := by rw [hc]; group

/-- For involutive `c`, the marked compression word is exactly the square of
the distinguished pointwise compression defect. -/
theorem word_eq_compressionDefect_sq
    (D : MarkedCompressionInclusionData Gamma E) (hc : D.c ^ 2 = 1) :
    D.word = ⁅D.t * D.c * D.t⁻¹, D.iota D.a⁆ ^ 2 := by
  rw [word, markedCompressionWord]
  exact commutator_conjugate_eq_commutator_sq_of_sq_eq_one
    (D.t * D.c * D.t⁻¹) (D.iota D.a) (D.transported_sq_eq_one hc)

/-- The manuscript's marked word belongs to the normal closure of all
pointwise compression defects. -/
theorem word_mem_compressionDefectNormal_of_c_sq_eq_one
    (D : MarkedCompressionInclusionData Gamma E) (hc : D.c ^ 2 = 1) :
    D.word ∈ D.compressionDefectNormal := by
  rw [D.word_eq_compressionDefect_sq hc, pow_two]
  exact mul_mem
    (Subgroup.subset_normalClosure ⟨D.a, rfl⟩)
    (Subgroup.subset_normalClosure ⟨D.a, rfl⟩)

end MarkedCompressionInclusionData

end GroupApproximation
