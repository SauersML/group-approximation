import NonsoficGroupsExist.Kazhdan.InvariantSubsetRounding
import NonsoficGroupsExist.KunThom.KunThomDiagonal

/-!
# Exact Kazhdan rounding for finite diagonal relations

An exact finite action on `Y` induces an exact diagonal action on `Y × Y`.
This file specializes invariant-subset rounding to that action.  Starting
from an arbitrary finite binary relation, it constructs an exactly invariant
relation whose symmetric-difference cost is bounded by the total labelled
diagonal boundary.

There are no representation-theoretic hypotheses hidden in the construction:
the only input to the quantitative theorem is an explicit `IsKazhdanPair`.
-/

namespace NonsoficGroupsExist
namespace DiagonalInvariantRelation

open scoped symmDiff
open KazhdanImprovement

universe u

variable {G : Type u} [Group G]
variable {Y : FiniteModel}

/-- The exact action on ordered pairs induced by an exact action on `Y`. -/
def diagonalActionHom (σ : G →* Equiv.Perm Y) :
    G →* Equiv.Perm (Y × Y) where
  toFun g := KunThomDiagonal.diagonalPerm (σ g)
  map_one' := by simp
  map_mul' g h := by simp

@[simp] theorem diagonalActionHom_apply (σ : G →* Equiv.Perm Y)
    (g : G) (p : Y × Y) :
    diagonalActionHom σ g p = (σ g p.1, σ g p.2) := rfl

/-- Total generator-labelled diagonal boundary.  The sum retains labels even
when two group elements happen to induce the same finite permutation. -/
def totalDiagonalBoundary (σ : G →* Equiv.Perm Y) (Q : Finset G)
    (U : Finset (Y × Y)) : ℕ :=
  ∑ q ∈ Q,
    ((U.map (diagonalActionHom σ q).toEmbedding) ∆ U).card

/-- The canonical relation obtained by invariant projection and thresholding
at `1/2` for the exact diagonal action. -/
noncomputable def roundedDiagonalRelation (σ : G →* Equiv.Perm Y)
    (U : Finset (Y × Y)) : Finset (Y × Y) :=
  KazhdanInvariantRounding.roundedInvariantSet (diagonalActionHom σ) U

/-- The rounded relation is exactly invariant under every group element. -/
theorem roundedDiagonalRelation_map (σ : G →* Equiv.Perm Y)
    (U : Finset (Y × Y)) (g : G) :
    (roundedDiagonalRelation σ U).map
        (diagonalActionHom σ g).toEmbedding =
      roundedDiagonalRelation σ U := by
  exact KazhdanInvariantRounding.roundedInvariantSet_map
    (diagonalActionHom σ) U g

/-- Quantitative exact diagonal-relation rounding.  The division-free form is
valid without any auxiliary nonzero assumption on the Kazhdan constant. -/
theorem kazhdan_mul_card_symmDiff_roundedDiagonalRelation_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σ : G →* Equiv.Perm Y) (U : Finset (Y × Y)) :
    ε ^ 2 * (((U ∆ roundedDiagonalRelation σ U).card : ℕ) : ℝ) ≤
      4 * (totalDiagonalBoundary σ Q U : ℝ) := by
  simpa only [roundedDiagonalRelation, totalDiagonalBoundary, Nat.cast_sum,
    Nat.cast_ofNat] using
      KazhdanInvariantRounding.kazhdan_mul_card_symmDiff_rounded_le_boundary
        hQ (diagonalActionHom σ) U

/-! ## Permutation graphs -/

/-- For one label, the forward diagonal boundary used by
`KazhdanImprovement` has exactly the cardinality of the symmetric difference
between the relation and its image. -/
theorem card_relationBoundary_singleton_eq_symmDiff_map
    (s : Equiv.Perm Y) (U : Finset (Y × Y)) :
    (relationBoundary Y {s} U).card =
      ((U.map (KunThomDiagonal.diagonalPerm s).toEmbedding) ∆ U).card := by
  apply Finset.card_bij (fun p _ ↦ diagonalAction Y p.1 p.2)
  · intro p hp
    have hpdata := (mem_relationBoundary Y {s} U p).1 hp
    rcases hpdata.2 with hout | hin
    · rw [Finset.mem_symmDiff]
      left
      refine ⟨Finset.mem_map.mpr ⟨p.2, hout.1, ?_⟩, hout.2⟩
      rw [show p.1 = s by simpa using hpdata.1]
      rfl
    · rw [Finset.mem_symmDiff]
      right
      refine ⟨hin.2, ?_⟩
      intro hmap
      rw [Finset.mem_map] at hmap
      obtain ⟨z, hzU, hz⟩ := hmap
      have hpEq : p.1 = s := by simpa using hpdata.1
      have hzp : z = p.2 := by
        apply (KunThomDiagonal.diagonalPerm s).injective
        simpa [hpEq, diagonalAction] using hz
      exact hin.1 (by simpa [hzp] using hzU)
  · intro p hp q hq heq
    have hpdata := (mem_relationBoundary Y {s} U p).1 hp
    have hqdata := (mem_relationBoundary Y {s} U q).1 hq
    have hpLabel : p.1 = s := by simpa using hpdata.1
    have hqLabel : q.1 = s := by simpa using hqdata.1
    apply Prod.ext (hpLabel.trans hqLabel.symm)
    exact (KunThomDiagonal.diagonalPerm s).injective (by
      simpa [hpLabel, hqLabel, diagonalAction] using heq)
  · intro y hy
    rw [Finset.mem_symmDiff] at hy
    let p : Equiv.Perm Y × (Y × Y) :=
      (s, (KunThomDiagonal.diagonalPerm s).symm y)
    have hdiag : diagonalAction Y s p.2 = y := by
      exact (KunThomDiagonal.diagonalPerm s).apply_symm_apply y
    refine ⟨p, ?_, ?_⟩
    · rw [mem_relationBoundary]
      refine ⟨Finset.mem_singleton_self s, ?_⟩
      rcases hy with ⟨hmap, hyU⟩ | ⟨hyU, hmap⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_map] at hmap
          obtain ⟨z, hzU, hz⟩ := hmap
          have hz : KunThomDiagonal.diagonalPerm s z = y := hz
          have hzpre : z = (KunThomDiagonal.diagonalPerm s).symm y := by
            apply (KunThomDiagonal.diagonalPerm s).injective
            simpa using hz
          simpa [p, hzpre] using hzU
        · simpa [show p.1 = s by rfl, hdiag] using hyU
      · right
        refine ⟨?_, ?_⟩
        · intro hpre
          apply hmap
          rw [Finset.mem_map]
          exact ⟨(KunThomDiagonal.diagonalPerm s).symm y, hpre, by simp⟩
        · simpa [show p.1 = s by rfl, hdiag] using hyU
    · exact hdiag

/-- The diagonal boundary of one permutation graph is controlled by twice
the corresponding commutation-defect count. -/
theorem card_symmDiff_diagonal_permutationGraph_le_two_badArcs
    (s c : Equiv.Perm Y) :
    (((permutationGraph Y c).map
        (KunThomDiagonal.diagonalPerm s).toEmbedding) ∆
      permutationGraph Y c).card ≤
        2 * (AlmostAutomorphism.badArcs Y {s} c).card := by
  rw [← card_relationBoundary_singleton_eq_symmDiff_map]
  exact card_relationBoundary_permutationGraph_le Y {s} c

/-- Total labelled commutation defect of a permutation against an exact
finite action. -/
def totalCommutationDefect (σ : G →* Equiv.Perm Y) (Q : Finset G)
    (c : Equiv.Perm Y) : ℕ :=
  ∑ q ∈ Q, (AlmostAutomorphism.badArcs Y {σ q} c).card

theorem totalDiagonalBoundary_permutationGraph_le
    (σ : G →* Equiv.Perm Y) (Q : Finset G) (c : Equiv.Perm Y) :
    totalDiagonalBoundary σ Q (permutationGraph Y c) ≤
      2 * totalCommutationDefect σ Q c := by
  rw [totalDiagonalBoundary, totalCommutationDefect, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  exact card_symmDiff_diagonal_permutationGraph_le_two_badArcs (σ q) c

/-- A permutation graph rounds to an exactly invariant relation with edit
cost controlled directly by its total commutation defect. -/
theorem kazhdan_mul_card_graph_symmDiff_rounded_le_defect
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, 0} G Q ε)
    (σ : G →* Equiv.Perm Y) (c : Equiv.Perm Y) :
    ε ^ 2 *
        ((((permutationGraph Y c) ∆
          roundedDiagonalRelation σ (permutationGraph Y c)).card : ℕ) : ℝ) ≤
      8 * (totalCommutationDefect σ Q c : ℝ) := by
  have hround := kazhdan_mul_card_symmDiff_roundedDiagonalRelation_le
    hQ σ (permutationGraph Y c)
  have hboundary := totalDiagonalBoundary_permutationGraph_le σ Q c
  have hboundaryReal :
      (totalDiagonalBoundary σ Q (permutationGraph Y c) : ℝ) ≤
        2 * totalCommutationDefect σ Q c := by
    exact_mod_cast hboundary
  nlinarith

/-! ## Returning from invariant relations to permutations -/

/-- Membership in the rounded relation is preserved in both directions by
every diagonal group element. -/
theorem mem_roundedDiagonalRelation_iff_action
    (σ : G →* Equiv.Perm Y) (U : Finset (Y × Y)) (g : G) (p : Y × Y) :
    p ∈ roundedDiagonalRelation σ U ↔
      diagonalAction Y (σ g) p ∈ roundedDiagonalRelation σ U := by
  constructor
  · intro hp
    rw [← roundedDiagonalRelation_map σ U g]
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
  · intro hp
    rw [← roundedDiagonalRelation_map σ U g⁻¹]
    refine Finset.mem_map.mpr
      ⟨diagonalAction Y (σ g) p, hp, ?_⟩
    change diagonalAction Y (σ g⁻¹) (diagonalAction Y (σ g) p) = p
    simp [diagonalAction]

/-- Consequently the tagged diagonal boundary of the rounded relation is
literally empty for the image of any finite label set. -/
theorem relationBoundary_roundedDiagonalRelation_eq_empty
    (σ : G →* Equiv.Perm Y) (Q : Finset G) (U : Finset (Y × Y)) :
    relationBoundary Y (Q.image σ) (roundedDiagonalRelation σ U) = ∅ := by
  ext p
  simp only [Finset.notMem_empty, iff_false]
  intro hp
  have hpdata := (mem_relationBoundary Y (Q.image σ)
    (roundedDiagonalRelation σ U) p).1 hp
  rw [Finset.mem_image] at hpdata
  obtain ⟨g, hgQ, hg⟩ := hpdata.1
  have hiff := mem_roundedDiagonalRelation_iff_action σ U g p.2
  rw [hg] at hiff
  rcases hpdata.2 with hout | hin
  · exact hout.2 (hiff.mp hout.1)
  · exact hin.1 (hiff.mpr hin.2)

/-- Extend the part of the original permutation graph retained by the
rounded invariant relation to a genuine permutation. -/
noncomputable def roundedDiagonalPermutation
    (σ : G →* Equiv.Perm Y) (c : Equiv.Perm Y) : Equiv.Perm Y :=
  roundRelation Y
    (roundedDiagonalRelation σ (permutationGraph Y c)) c

/-- The repaired permutation's labelled commutation defect is charged only
to the relation edits, because the rounded relation itself has zero diagonal
boundary. -/
theorem card_badArcs_roundedDiagonalPermutation_le
    (σ : G →* Equiv.Perm Y) (Q : Finset G) (c : Equiv.Perm Y) :
    (AlmostAutomorphism.badArcs Y (Q.image σ)
      (roundedDiagonalPermutation σ c)).card ≤
      (Q.image σ).card *
        ((permutationGraph Y c ∆
          roundedDiagonalRelation σ (permutationGraph Y c)).card) := by
  let U := roundedDiagonalRelation σ (permutationGraph Y c)
  have hbase := card_badArcs_roundRelation_le Y (Q.image σ) U c
  have hboundary : relationBoundary Y (Q.image σ) U = ∅ :=
    relationBoundary_roundedDiagonalRelation_eq_empty σ Q
      (permutationGraph Y c)
  have hedits :
      (permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card =
        (permutationGraph Y c ∆ U).card := by
    rw [Finset.symmDiff_def,
      Finset.card_union_of_disjoint (by
        simp only [Finset.disjoint_left, Finset.mem_sdiff]
        aesop)]
  rw [hboundary, Finset.card_empty, zero_add, hedits] at hbase
  simpa [roundedDiagonalPermutation, U] using hbase

/-- The repaired permutation differs from the original only at graph points
discarded by the rounded relation. -/
theorem card_hammingDisagreement_roundedDiagonalPermutation_le
    (σ : G →* Equiv.Perm Y) (c : Equiv.Perm Y) :
    (hammingDisagreement (roundedDiagonalPermutation σ c) c).card ≤
      (permutationGraph Y c ∆
        roundedDiagonalRelation σ (permutationGraph Y c)).card := by
  let U := roundedDiagonalRelation σ (permutationGraph Y c)
  have hsubset := roundRelation_disagreement_subset_missingSources Y U c
  have hcard := Finset.card_le_card hsubset
  rw [card_missingSources] at hcard
  have hsdiff : permutationGraph Y c \ U ⊆ permutationGraph Y c ∆ U := by
    intro p hp
    exact (Finset.mem_symmDiff).2 (Or.inl (Finset.mem_sdiff.mp hp))
  have hmissing := Finset.card_le_card hsdiff
  simpa [roundedDiagonalPermutation, hammingDisagreement, U] using
    hcard.trans hmissing

end DiagonalInvariantRelation
end NonsoficGroupsExist
