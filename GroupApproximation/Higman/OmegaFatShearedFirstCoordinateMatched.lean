import GroupApproximation.Higman.OmegaFatShearedCoordinateShift

/-!
# A concrete matched finite cutter for the first sheared coordinate

The one-coordinate block alphabet is literally `ℤ`.  Centering at a
coefficient `n` and then using Higman's free row embedding sends the `n`th
coefficient slice to the same cyclic subgroup `⟨row 0⟩ ≤ Row.F₀`.
Thus one finitely presented torsion-free ambient and one finitely generated
cutter work simultaneously for every coefficient slice.  Adjacent centered
embeddings agree on the common singleton abstract basis, which is the exact
matched identity consumed by the first finite HNN step.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

/-- The block supported at coordinate zero with value `n`. -/
def blockSetOneOfInt (n : ℤ) : ↥(blockSet 1) :=
  ⟨Finsupp.single 0 n, by
    intro i hi
    rw [Finsupp.single_apply]
    by_cases hzero : (0 : ℤ) = i
    · subst i
      exact (hi (by simp)).elim
    · rw [if_neg hzero]⟩

/-- Evaluation at zero identifies the one-coordinate alphabet with `ℤ`. -/
def blockSetOneEquivInt : ↥(blockSet 1) ≃ ℤ where
  toFun beta := beta.1 0
  invFun := blockSetOneOfInt
  left_inv beta := by
    apply Subtype.ext
    ext i
    by_cases hi : i = 0
    · subst i
      simp [blockSetOneOfInt]
    · have houtside : i ∉ Finset.Ico (0 : ℤ) 1 := by
        intro hmem
        have hbounds := Finset.mem_Ico.mp hmem
        omega
      rw [beta.2 i houtside]
      simp [blockSetOneOfInt, Finsupp.single_apply, hi]
  right_inv n := by
    simp [blockSetOneOfInt]

/-- Recenter the one-coordinate alphabet so that coefficient `n` has label
zero. -/
def blockSetOneCenteredEquivInt (n : ℤ) : ↥(blockSet 1) ≃ ℤ where
  toFun beta := beta.1 0 - n
  invFun z := blockSetOneOfInt (z + n)
  left_inv beta := by
    apply Subtype.ext
    apply (blockSetOneEquivInt.injective)
    change beta.1 0 - n + n = beta.1 0
    omega
  right_inv z := by
    change z + n - n = z
    omega

/-- The free alphabet, recentered at coefficient `n`. -/
noncomputable def blockSetOneCenteredFreeEquiv (n : ℤ) :
    FreeGroup ↥(blockSet 1) ≃* FreeGroup ℤ :=
  FreeGroup.freeGroupCongr (blockSetOneCenteredEquivInt n)

/-- All coefficient slices embed in the same finite row ambient; only the
centering of the alphabet changes. -/
noncomputable def firstCoordinateMatchedEmb (n : ℤ) :
    FreeGroup ↥(blockSet 1) →* Row.F₀ :=
  Row.basisHom.comp (blockSetOneCenteredFreeEquiv n).toMonoidHom

theorem firstCoordinateMatchedEmb_injective (n : ℤ) :
    Function.Injective (firstCoordinateMatchedEmb n) :=
  Row.basisHom_injective.comp (blockSetOneCenteredFreeEquiv n).injective

@[simp] theorem firstCoordinateMatchedEmb_of
    (n : ℤ) (beta : ↥(blockSet 1)) :
    firstCoordinateMatchedEmb n (FreeGroup.of beta) =
      Row.row (beta.1 0 - n) := by
  rw [firstCoordinateMatchedEmb, MonoidHom.comp_apply]
  change Row.basisHom (FreeGroup.of (beta.1 0 - n)) = _
  rw [Row.basisHom_of]

/-- The basis letters in the coefficient-`n` slice. -/
def firstCoordinateSlice (n : ℤ) : Set ↥(blockSet 1) :=
  {beta | beta.1 0 = n}

/-- The free coordinate subgroup belonging to one coefficient slice. -/
def firstCoordinateSliceSubgroup (n : ℤ) :
    Subgroup (FreeGroup ↥(blockSet 1)) :=
  Subgroup.closure (FreeGroup.of '' firstCoordinateSlice n)

/-- The single cutter reused for every centered coefficient slice. -/
def firstCoordinateMatchedCutter : Subgroup Row.F₀ :=
  Subgroup.closure {Row.row 0}

theorem firstCoordinateMatchedCutter_fg : firstCoordinateMatchedCutter.FG :=
  (Subgroup.fg_iff _).mpr
    ⟨{Row.row 0}, rfl, Set.finite_singleton _⟩

/-- Every centered slice maps exactly onto the common cyclic cutter. -/
theorem map_firstCoordinateSliceSubgroup (n : ℤ) :
    (firstCoordinateSliceSubgroup n).map (firstCoordinateMatchedEmb n) =
      firstCoordinateMatchedCutter := by
  unfold firstCoordinateSliceSubgroup firstCoordinateMatchedCutter
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨beta, hbeta, rfl⟩, rfl⟩
    rw [firstCoordinateMatchedEmb_of, hbeta]
    simp
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨FreeGroup.of (blockSetOneOfInt n), ?_, ?_⟩
    · exact ⟨blockSetOneOfInt n, by simp [firstCoordinateSlice,
        blockSetOneOfInt], rfl⟩
    · simp

/-- Exact comap: the common finite cutter cuts precisely the requested
coefficient slice under the centered embedding. -/
theorem firstCoordinateMatchedCutter_comap (n : ℤ) :
    firstCoordinateMatchedCutter.comap (firstCoordinateMatchedEmb n) =
      firstCoordinateSliceSubgroup n := by
  rw [← map_firstCoordinateSliceSubgroup n]
  exact Subgroup.comap_map_eq_self_of_injective
    (firstCoordinateMatchedEmb_injective n) _

/-- A coefficient slice as a copy of the width-zero singleton alphabet. -/
def firstCoordinateSliceIncl (n : ℤ) :
    ↥(blockSet 0) → ↥(blockSet 1) :=
  fun _ => blockSetOneOfInt n

/-- Adjacent centered embeddings evaluate the same abstract width-zero word
to exactly the same element of the shared finite ambient. -/
theorem firstCoordinateMatched_restrict_eq (n : ℤ) :
    (firstCoordinateMatchedEmb (n + 1)).comp
        (FreeGroup.map (firstCoordinateSliceIncl (n + 1))) =
      (firstCoordinateMatchedEmb n).comp
        (FreeGroup.map (firstCoordinateSliceIncl n)) := by
  refine FreeGroup.ext_hom _ _ fun beta ↦ ?_
  simp [firstCoordinateSliceIncl, blockSetOneOfInt]

/-- The concrete torsion-free benign witness cut out by the shared row
ambient at coefficient `n`. -/
noncomputable def firstCoordinateMatchedWitness (n : ℤ) :
    TorsionFreeBenignWitness (firstCoordinateSliceSubgroup n) where
  witness :=
    { K := Row.F₀
      emb := firstCoordinateMatchedEmb n
      emb_injective := firstCoordinateMatchedEmb_injective n
      L := firstCoordinateMatchedCutter
      L_fg := firstCoordinateMatchedCutter_fg
      comap_eq := firstCoordinateMatchedCutter_comap n }
  torsionFree := IsPowerTorsionFree.of_isMulTorsionFree

end Omega
end Higman
end GroupApproximation
