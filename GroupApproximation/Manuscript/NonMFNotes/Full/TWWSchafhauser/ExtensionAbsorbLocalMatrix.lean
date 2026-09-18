import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionAbsorbLocalState
import GroupApproximation.Analysis.CStarExactness

/-!
# Matrix blocks of completely positive maps

Lane `TWWSch3c2C2`, work order `WO-TWWSch-3c2-C2`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), absorption step. Source: G. A. Elliott and
D. Kucerovsky, Pacific J. Math. 198 (2001), proof of Thm. 6 (reduction of a nuclear map into
the compacts to finite-dimensional pieces).

A completely positive `α : S → D` into a finite-dimensional C*-algebra, followed by a matrix
picture `e : D → M_Y`, and compact operators `b : Y → 𝓑(H_J)` give the block
`s ↦ ∑ᵢ ∑ⱼ e(α s)ᵢⱼ bᵢ⋆ bⱼ`. The lift `ℓ` is **matrix-compressible** when every such block is
locally compressible into `ℓ`. The nuclear reduction (`ExtensionAbsorbLocalNuclear`) turns
matrix-compressibility into compressibility of `s ↦ k⋆ σ(s) k`. The Elliott--Kucerovsky
Lemma 7 (`WO-TWWSch-3c2-C2-X`) together with the excisable-state approximation of completely
positive maps into matrices (`WO-TWWSch-3c2-C2-Y`) yields it from state-compressibility.

Nothing here has been compiled (lane rule).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule GroupApproximation.CStarExactness

noncomputable section

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The block `s ↦ ∑ᵢ ∑ⱼ f(s)ᵢⱼ bᵢ⋆ bⱼ` of a matrix-valued map (Elliott--Kucerovsky 2001,
proof of Thm. 6; `non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def matrixBlockMap {Y : Type} [Fintype Y] (f : S → Matrix Y Y ℂ) (b : Y → StdBdd J) :
    S → StdBdd J :=
  fun s => ∑ i, ∑ j, f s i j • (star (b i) * b j)

/-- `ℓ` is **matrix-compressible**: for every completely positive `α : S → D` into a
finite-dimensional C*-algebra, every matrix picture `e : D →⋆ₐ M_Y` and all compact `bᵢ`, the
block `matrixBlockMap (e ∘ α) b` is locally compressible into `ℓ` (Elliott--Kucerovsky 2001,
Lemma 7 and proof of Thm. 6; `non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
def IsMatrixCompressible (ℓ : S → StdBdd J) : Prop :=
  ∀ (D : FinDimCStarAlgebra) (α : S →ₗ[ℂ] D), IsCompletelyPositive α →
    ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (e : D →⋆ₐ[ℂ] Matrix Y Y ℂ) (b : Y → StdBdd J),
      (∀ i, IsStdCompact (b i)) → IsLocallyCompressible ℓ (matrixBlockMap (fun s => e (α s)) b)

/-- Finite sums of matrix blocks with a common completely positive map are compressible into
a matrix-compressible lift (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
theorem IsMatrixCompressible.sum {ℓ : S → StdBdd J} (hℓ : IsMatrixCompressible ℓ)
    (D : FinDimCStarAlgebra) (α : S →ₗ[ℂ] D) (hα : IsCompletelyPositive α)
    {Y : Type} [Fintype Y] [DecidableEq Y] (e : D →⋆ₐ[ℂ] Matrix Y Y ℂ)
    {κ : Type} (t : Finset κ) (b : κ → Y → StdBdd J) (hb : ∀ m ∈ t, ∀ i, IsStdCompact (b m i)) :
    IsLocallyCompressible ℓ
      (fun s => ∑ m ∈ t, matrixBlockMap (fun s => e (α s)) (b m) s) :=
  isLocallyCompressible_sum t fun m hm => hℓ D α hα e (b m) (hb m hm)

end

end GroupApproximation.Full.TWWSchafhauser
