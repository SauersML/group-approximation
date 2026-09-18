import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFUltrapowerTrace
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Star.Subalgebra

/-!
# The block embeddings `M_k(M_{m!}) → M_k(Q)`

Lane `TWWSch3d2Q1` (work order `WO-TWWSch-3d2-Q1`, items (2)--(4)).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4, which uses the minimal K-theory of the universal
UHF algebra `Q` (Rørdam--Larsen--Laustsen, *An introduction to K-theory for
C⋆-algebras*, Ex. 7.7.7; Davidson, *C⋆-algebras by example*, III.5).

For `M : UHFModel Q`, the `m`-th building block `ι m : M_{m!} → Q` amplifies to the
star algebra homomorphism
`blockHom m k : M_{k · m!}(ℂ) ≅ M_k(M_{m!}) → M_k(Q)`,
whose `(i, j)` entry is `ι m` of the `(i, j)` block.  We record:

* it is injective (`expect m ∘ ι m = id` entrywise);
* the matrix trace `∑ i, tr_Q (x i i)` of its image is `Tr / m!`;
* its image has finite spectrum (spectra only shrink under algebra maps);
* the matrix trace over `Q` is tracial.

These are the finite-dimensional ingredients of items (2)--(4).

## Main declarations

* `UHFModel.blockHom`, `UHFModel.blockHom_apply`, `UHFModel.blockHom_injective`;
* `UHFModel.uhfK_sum_trace_blockHom`, `UHFModel.uhfK_sum_trace_mul_comm`;
* `UHFModel.uhfK_finite_spectrum_blockHom`;
* `UHFModel.blockRange`, `UHFModel.mem_blockRange`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

noncomputable section

/-- The `(i, j)` block of a matrix indexed by `Fin k × M_{m!}`-indices (the block
decomposition behind the amplified inclusions of `Q`,
`thm:fixed-radical-membership` in `non_mf_group_notes.tex`). -/
def uhfK_blockEntry {m k : ℕ} (a : Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ)
    (i j : Fin k) : Matrix (uhfLevel m) (uhfLevel m) ℂ :=
  Matrix.of fun r s => a (i, r) (j, s)

/-- Blocks of the adjoint are adjoints of the transposed blocks. -/
theorem uhfK_blockEntry_star {m k : ℕ}
    (a : Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ) (i j : Fin k) :
    uhfK_blockEntry (star a) i j = star (uhfK_blockEntry a j i) :=
  Matrix.ext fun _ _ => rfl

namespace UHFModel

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q)

/-- The amplified inclusion `M_{k · m!}(ℂ) ≅ M_k(M_{m!}) → M_k(Q)` as a star algebra
homomorphism of plain matrices (Schafhauser, Crelle 759 (2020), §4, used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`). -/
def blockStarAlgHom (m k : ℕ) :
    Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ →⋆ₐ[ℂ] Matrix (Fin k) (Fin k) Q :=
  { (M.ι m).toAlgHom.mapMatrix.comp
      (Matrix.compAlgEquiv (Fin k) (uhfLevel m) ℂ ℂ).symm.toAlgHom with
    map_star' := fun a => by
      ext i j
      change M.ι m (uhfK_blockEntry (star a) i j) = star (M.ι m (uhfK_blockEntry a j i))
      rw [uhfK_blockEntry_star, map_star] }

/-- **The amplified inclusion `M_{k · m!}(ℂ) → M_k(Q)`**, landing in the C⋆-matrix
algebra `CStarMatrix (Fin k) (Fin k) Q` (`thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
def blockHom (m k : ℕ) :
    Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ →⋆ₐ[ℂ]
      CStarMatrix (Fin k) (Fin k) Q :=
  (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin k) (A := Q)).toStarAlgHom.comp
    (M.blockStarAlgHom m k)

/-- The entries of the amplified inclusion. -/
theorem blockHom_apply {m k : ℕ} (a : Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ)
    (i j : Fin k) : M.blockHom m k a i j = M.ι m (uhfK_blockEntry a i j) :=
  rfl

/-- The amplified inclusion is injective, since `expect m ∘ ι m = id`. -/
theorem blockHom_injective (m k : ℕ) : Function.Injective (M.blockHom m k) := by
  intro a b h
  ext ⟨i, r⟩ ⟨j, s⟩
  have hij : M.ι m (uhfK_blockEntry a i j) = M.ι m (uhfK_blockEntry b i j) := by
    rw [← M.blockHom_apply, ← M.blockHom_apply, h]
  have := congrArg (M.expect m) hij
  rw [M.expect_ι, M.expect_ι] at this
  exact congrFun (congrFun this r) s

/-- The trace of `Q` on a building block, as `Tr / m!`. -/
theorem uhfK_trace_ι_div (m : ℕ) (x : Matrix (uhfLevel m) (uhfLevel m) ℂ) :
    M.trace (M.ι m x) = Matrix.trace x / (m.factorial : ℂ) := by
  rw [M.trace_ι, normTrace, card_uhfLevel]

/-- **The matrix trace over `Q` is tracial**: `∑ i, tr_Q ((a b) i i) = ∑ i, tr_Q ((b a) i i)`
(`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem uhfK_sum_trace_mul_comm {k : ℕ} (a b : CStarMatrix (Fin k) (Fin k) Q) :
    ∑ i, M.trace ((a * b) i i) = ∑ i, M.trace ((b * a) i i) := by
  have e : ∀ (c d : CStarMatrix (Fin k) (Fin k) Q) (i : Fin k),
      (c * d) i i = ∑ j, c i j * d j i := fun _ _ _ => rfl
  simp only [e, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => M.trace_mul_comm _ _

/-- **The matrix trace of an amplified block is `Tr / m!`**
(`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem uhfK_sum_trace_blockHom (m k : ℕ)
    (a : Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ) :
    ∑ i, M.trace (M.blockHom m k a i i) = Matrix.trace a / (m.factorial : ℂ) := by
  have h : ∀ i, M.trace (M.blockHom m k a i i) =
      Matrix.trace (uhfK_blockEntry a i i) / (m.factorial : ℂ) := fun i => by
    rw [M.blockHom_apply]
    exact M.uhfK_trace_ι_div m _
  simp only [h]
  rw [← Finset.sum_div]
  congr 1
  exact (Fintype.sum_prod_type fun x => a x x).symm

/-- **Amplified blocks have finite spectrum**: spectra shrink under the algebra map
`blockHom`, and matrices over `ℂ` have finite spectrum. -/
theorem uhfK_finite_spectrum_blockHom (m k : ℕ)
    (a : Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ) :
    (spectrum ℂ (M.blockHom m k a)).Finite :=
  (Matrix.finite_spectrum a).subset (AlgHom.spectrum_apply_subset (M.blockHom m k) a)

/-- The image of the amplified inclusion, a star subalgebra of `M_k(Q)`. -/
def blockRange (m k : ℕ) : StarSubalgebra ℂ (CStarMatrix (Fin k) (Fin k) Q) :=
  (⊤ : StarSubalgebra ℂ (Matrix (Fin k × uhfLevel m) (Fin k × uhfLevel m) ℂ)).map
    (M.blockHom m k)

/-- Membership in the image of the amplified inclusion. -/
theorem mem_blockRange {m k : ℕ} {y : CStarMatrix (Fin k) (Fin k) Q} :
    y ∈ M.blockRange m k ↔ ∃ a, M.blockHom m k a = y := by
  rw [blockRange, StarSubalgebra.mem_map]
  exact ⟨fun ⟨a, _, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, StarSubalgebra.mem_top, ha⟩⟩

end UHFModel

end

end GroupApproximation.Full.TWWSchafhauser
