import GroupApproximation.Leavitt.ElementaryPerfect
import GroupApproximation.Leavitt.FamilyRankFour
import Mathlib.GroupTheory.IsPerfect

/-!
# A strict central-cover witness in the binary Leavitt rank-four group

The rank-four compressor conjugates the rank-three elementary core onto its
compressed image.  The complementary corner witness centralizes that image,
but an explicit elementary transvection in the uncompressed core does not
commute with the first corner generator.  This packages those facts in the
exact subgroup form consumed by the central-cover inheritance theorem.
-/

namespace GroupApproximation
namespace LeavittStrictCentralCoverWitness

noncomputable section

variable {A : Type} [Ring A] [Nontrivial A]

abbrev Core (A : Type) [Ring A] := RankFour.Core A
abbrev Ambient (A : Type) [Ring A] := RankFour.Ambient A

/-- The compressed rank-three core inside the rank-four ambient group. -/
def compressedEmbedding (L : LeavittFamily A) : Core A →* Ambient A :=
  RankFour.coreEmbedding.comp (RankFour.compressionEnd L)

/-- Regard the ambient group as the subgroup used by the inheritance API. -/
abbrev AmbientTop (A : Type) [Ring A] : Subgroup (Ambient A) := ⊤

/-- The compressed embedding with codomain bundled as the ambient top
subgroup. -/
def compressedEmbeddingTop (L : LeavittFamily A) : Core A →* AmbientTop A :=
  (compressedEmbedding L).codRestrict ⊤ (fun _ ↦ Subgroup.mem_top _)

/-- The conjugated rank-three core, as a subgroup of the ambient top
subgroup. -/
def CompressedCore (L : LeavittFamily A) : Subgroup (AmbientTop A) :=
  (compressedEmbeddingTop L).range

instance compressedCore_isPerfect (L : LeavittFamily A) :
    Group.IsPerfect (CompressedCore L) := by
  letI : Group.IsPerfect (Core A) :=
    ⟨elementaryGroup_commutator_eq_top 3 (by omega)⟩
  exact Group.IsPerfect.range (compressedEmbeddingTop L)

/-- The elementary transvection used to detect that the corner witness is
not central in the uncompressed core. -/
def testRoot (A : Type) [Ring A] : Core A :=
  elementaryRoot (R := A) (0 : Fin 3) 1 (by decide) 1

/-- The first explicit complementary-corner witness, embedded in the
rank-four ambient group. -/
def witness (L : LeavittFamily A) : Ambient A :=
  RankFour.coreEmbedding (FamilyRankFour.witnessEmbedding L L.cornerWitnessA)

/-- The distinguished compressor, bundled in the ambient top subgroup. -/
def compressor (L : LeavittFamily A) : AmbientTop A :=
  ⟨RankFour.compressor L, Subgroup.mem_top _⟩

/-- The compressed test root, bundled as an element of the compressed core. -/
def compressedTestRoot (L : LeavittFamily A) : CompressedCore L :=
  ⟨compressedEmbeddingTop L (testRoot A),
    ⟨testRoot A, rfl⟩⟩

/-- The first corner generator is nontrivial. -/
theorem cornerWitnessA_ne_one (L : LeavittFamily A) :
    L.cornerWitnessA ≠ 1 := by
  intro hA
  apply L.generators_not_commute
  have hA' : L.generatorA = 1 := by
    apply L.cornerHom_injective
    have h := congrArg Subtype.val hA
    simpa [LeavittFamily.cornerWitnessA] using h
  simp [hA']

/-- A first-coordinate diagonal unit commutes with the `(0,1)` unit
transvection only when that diagonal coefficient is one. -/
theorem witnessEmbedding_not_commute_testRoot (L : LeavittFamily A) :
    ¬ Commute (FamilyRankFour.witnessEmbedding L L.cornerWitnessA) (testRoot A) := by
  intro hcomm
  have hentry := congrArg
    (fun z : Core A ↦
      ((↑(z : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) 0 1))
    hcomm.eq
  have hcorner :
      (L.cornerHom L.generatorA : Aˣ) = 1 := by
    apply Units.ext
    simpa [FamilyRankFour.witnessEmbedding,
      LeavittFamily.cornerWitnessA, testRoot, elementaryRoot,
      elementaryUnit, Matrix.mul_apply, Fin.sum_univ_succ,
      DiagonalElementary.firstDiagonalUnitHom_apply] using hentry
  apply cornerWitnessA_ne_one L
  apply Subtype.ext
  simpa [LeavittFamily.cornerWitnessA] using hcorner

/-- The ambient corner witness does not commute with the embedded test root. -/
theorem witness_not_commute_coreTestRoot (L : LeavittFamily A) :
    ¬ Commute (witness L) (RankFour.coreEmbedding (testRoot A)) := by
  intro hcomm
  apply witnessEmbedding_not_commute_testRoot L
  apply RankFour.coreEmbedding_injective
  simpa [witness, map_mul] using hcomm.eq

omit [Nontrivial A] in
/-- Every element of the compressed core commutes with the corner witness. -/
theorem witness_centralizes_compressedCore (L : LeavittFamily A)
    (g : AmbientTop A) (hg : g ∈ CompressedCore L) :
    Commute (witness L) ((AmbientTop A).subtype g) := by
  obtain ⟨x, rfl⟩ := hg
  exact ((FamilyRankFour.compressionEnd_commutes_witnessEmbedding
    L x L.cornerWitnessA).symm.map RankFour.coreEmbedding)

omit [Nontrivial A] in
/-- Conjugating the compressed test root back by the compressor recovers
the ordinary core test root. -/
theorem compressor_inv_conjugate_compressedTestRoot (L : LeavittFamily A) :
    (AmbientTop A).subtype
        ((compressor L)⁻¹ * (compressedTestRoot L : AmbientTop A) * compressor L) =
      RankFour.coreEmbedding (testRoot A) := by
  change (RankFour.compressor L)⁻¹ *
      compressedEmbedding L (testRoot A) * RankFour.compressor L = _
  rw [show compressedEmbedding L (testRoot A) =
      RankFour.compressor L * RankFour.coreEmbedding (testRoot A) *
        (RankFour.compressor L)⁻¹ by
    exact RankFour.compressorSet_conjugation L (RankFour.compressor L)
      (RankFour.compressor_mem L) (testRoot A)]
  group

/-- The strict failure of centralization required by the Kun--Thom
central-cover inheritance theorem. -/
theorem witness_strict (L : LeavittFamily A) :
    ¬ Commute (witness L)
      ((AmbientTop A).subtype
        ((compressor L)⁻¹ * (compressedTestRoot L : AmbientTop A) * compressor L)) := by
  rw [compressor_inv_conjugate_compressedTestRoot]
  exact witness_not_commute_coreTestRoot L

end
end LeavittStrictCentralCoverWitness
end GroupApproximation
