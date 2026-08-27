import GroupApproximation.Analysis.PrintedCornerCompression
import GroupApproximation.Analysis.PrintedDiagonalSubsequence
import GroupApproximation.Analysis.OmegaCoronaKazhdanProjection

/-!
# The compression paragraph, joined end to end

Proof-ledger row `NK.07`, last clause.  Three pieces of the printed paragraph
were in the development and were not joined:

* `OmegaCoronaKazhdanProjection.manuscriptComplementProjectionLift` lifts the
  complementary projection to coordinate projections `q_n`, nonzero on a set
  that lies in `ω`, with `‖[q_n, V_{g,n}]‖ →_ω 0`;
* `PrintedDiagonalSubsequence.exists_strictMono_mem_tendsto_atTop_countable`
  is the printed `A_j` extraction: it chooses `n₁ < n₂ < ⋯` *inside* a
  prescribed `ω`-large set while turning countably many `ω`-limits into
  ordinary ones;
* `PrintedCornerCompression.PrintedCornerData` packages the printed
  hypotheses at ordinary stages, and
  `manuscriptCornerAsymptoticRepresentation` compresses them to an
  `OpAlmostRepresentation` on nonzero corners.

The middle piece is what carries the first to the third, and the join is the
printed sentence "Enumerate `H̄ = {g₁, g₂, …}`": the family of sequences whose
`ω`-limits must become ordinary is indexed by `G` for the commutators and by
`G × G` for the multiplication defects, so it is countable exactly when the
group is, which is the printed hypothesis on `H̄`.  The `ω`-large set the
extraction is asked to stay inside is `{n | q_n ≠ 0}`, which is the printed
first clause of `A_j` and the reason the corners are nonzero.

`exists_printedCornerData` performs the join, and
`manuscriptCompressionParagraph` states its consequence on the printed
objects: an operator-norm asymptotic representation of the ambient group on
nonzero corners, obtained from the ultraproduct data alone.

## Manuscript status

Closes the last clause of `NK.07` end to end, from the ultraproduct lift.
-/

namespace GroupApproximation
namespace PrintedCornerAssembly

open Filter Matrix Topology
open AbstractSpectralGap VectorOmegaAction VectorOmegaCoronaAction
open VectorOmegaKazhdanGap VectorHilbertUltraproduct
open GroupApproximation.OmegaCoronaKazhdanProjection
open GroupApproximation.PrintedCornerCompression
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

variable (Y : ℕ → FiniteModel) (ω : Ultrafilter ℕ) [∀ n, Nonempty (Y n)]
variable {G : Type*} [Group G] [Countable G]

/-- The countable index of the printed enumeration: one sequence per group
element for the commutators, and one per pair for the multiplication
defects. -/
private abbrev Idx₂ (G : Type*) := G ⊕ G × G

/-- **The printed `A_j` join.**  From the `ω`-data of the compression
paragraph --- coordinate projections nonzero on an `ω`-large set, with
`ω`-vanishing commutators, over a coordinatewise-unitary family whose
multiplication defect is `ω`-null --- a subsequence produces the printed
ordinary-stage datum. -/
theorem exists_printedCornerData (hω : (ω : Filter ℕ) ≤ cofinite)
    (R : OmegaUnitaryRep Y ω G)
    (qn : BoundedMatrixSequence (Idx Y))
    (hproj : ∀ n, IsOrthogonalProjectionMatrix
      ((qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n))
    (hne : {n | (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n ≠ 0}
      ∈ (ω : Filter ℕ))
    (hcomm : ∀ g : G, IsNullMatrixSequence (Idx Y) (ω : Filter ℕ)
      (unitarySeq Y R.V g * qn - qn * unitarySeq Y R.V g)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (PrintedCornerData G (fun k ↦ Y (φ k))) := by
  classical
  -- the two families of sequences named in the printed `A_j`
  let a : G → BoundedMatrixSequence (Idx Y) := fun g ↦
    unitarySeq Y R.V g * qn - qn * unitarySeq Y R.V g
  let b : G × G → BoundedMatrixSequence (Idx Y) := fun p ↦
    unitarySeq Y R.V (p.1 * p.2)
      - unitarySeq Y R.V p.1 * unitarySeq Y R.V p.2
  let F : Idx₂ G → ℕ → ℝ :=
    Sum.elim
      (fun g n ↦ ‖((a g : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)‖)
      (fun p n ↦ ‖((b p : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n)‖)
  have hFlim : ∀ i : Idx₂ G, Tendsto (F i) (ω : Filter ℕ) (𝓝 0) := by
    rintro (g | ⟨g, h⟩)
    · exact hcomm g
    · exact R.mul_null g h
  obtain ⟨φ, hmono, hmem, hlim⟩ :=
    PrintedDiagonalSubsequence.exists_strictMono_mem_tendsto_atTop_countable
      hω hne F (fun _ ↦ 0) hFlim
  refine ⟨φ, hmono, ⟨?_⟩⟩
  refine
    { V := fun k g ↦ R.V (φ k) g
      q := fun k ↦ (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) (φ k)
      q_projection := fun k ↦ hproj (φ k)
      q_ne_zero := fun k ↦ hmem k
      mul_vanishing := ?_
      commutator_vanishing := ?_ }
  · intro g h
    exact hlim (Sum.inr (g, h))
  · intro g
    exact hlim (Sum.inl g)

/-- **The compression paragraph, on the printed objects.**  The ultraproduct
data of the compression paragraph yields, after the printed subsequence, an
operator-norm asymptotic representation of the ambient group on corners that
are all nonzero. -/
theorem manuscriptCompressionParagraph (hω : (ω : Filter ℕ) ≤ cofinite)
    (R : OmegaUnitaryRep Y ω G)
    (qn : BoundedMatrixSequence (Idx Y))
    (hproj : ∀ n, IsOrthogonalProjectionMatrix
      ((qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n))
    (hne : {n | (qn : ∀ n, Matrix (Idx Y n) (Idx Y n) ℂ) n ≠ 0}
      ∈ (ω : Filter ℕ))
    (hcomm : ∀ g : G, IsNullMatrixSequence (Idx Y) (ω : Filter ℕ)
      (unitarySeq Y R.V g * qn - qn * unitarySeq Y R.V g)) :
    ∃ (model : ℕ → FiniteModel) (D : PrintedCornerData G model),
      (∀ n, D.cornerRepresentation.model n = D.cornerModel n) ∧
        (∀ n, 0 < Fintype.card (D.cornerModel n)) ∧
        (∀ g : G, Tendsto (fun n ↦
          ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
            - D.compress n g‖) atTop (𝓝 0)) := by
  obtain ⟨φ, -, ⟨D⟩⟩ := exists_printedCornerData Y ω hω R qn hproj hne hcomm
  exact ⟨fun k ↦ Y (φ k), D, D.manuscriptCornerAsymptoticRepresentation⟩

end

end PrintedCornerAssembly
end GroupApproximation
