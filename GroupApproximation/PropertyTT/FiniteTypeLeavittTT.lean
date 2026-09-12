import GroupApproximation.KOne.AllRanksElementaryCore
import GroupApproximation.KOne.GLIsElementary
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Leavitt.LeavittRankEquivalence
import GroupApproximation.PropertyTT.BoundedGeneration
import GroupApproximation.PropertyTT.FiniteTypeRankFourRelativeTT
import GroupApproximation.PropertyTT.RankFourGlobalization
import GroupApproximation.PropertyTT.RelativeReindex
import GroupApproximation.PropertyTT.StabilizationCoordinateBlock

/-!
# `(TT)/T` for a natural class of finite-type Leavitt rings

This file isolates the general theorem behind the binary Leavitt example.
The coefficient ring is required to have:

* a finite-free characteristic-two presentation;
* a binary Leavitt family, giving matrix self-similarity;
* single-sandwich division;
* trivial elementary diagonal class.

The first two hypotheses supply the analytic rank-four input internally.  The
last two identify every finite-rank general linear group with its elementary
subgroup and give the uniform coordinate-block decomposition.
-/

namespace GroupApproximation
namespace FiniteTypeLeavittTT

open RankFourParabolicGeometry

noncomputable section

universe v

variable {R : Type} [Ring R] [Nontrivial R]

abbrev E3 := elementaryGroup (Fin 3) R
abbrev E4 := elementaryGroup (Fin 4) R
abbrev GL3 := (Matrix (Fin 3) (Fin 3) R)ˣ
abbrev GL4 := (Matrix (Fin 4) (Fin 4) R)ˣ

/-- The two ring-theoretic assumptions force `GLₙ(R) = ELₙ(R)` for every
`n ≥ 2` once `R` carries binary Leavitt self-similarity. -/
theorem elementaryGroup_eq_top
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 2 ≤ n) :
    elementaryGroup (Fin n) R = ⊤ := by
  have htwo : elementaryGroup (Fin 2) R = ⊤ := by
    rw [eq_top_iff]
    intro A _
    exact MatrixDiagonalization.mem_elementaryGroup_of_division_of_stable
      hdiv hdiag A
  exact L.elementaryGroup_eq_top_of_rankTwo htwo n hn

/-- The elementary rank-four group is canonically the full general linear
group under the class hypotheses. -/
noncomputable def elementaryEquivGL4
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R) : E4 (R := R) ≃* GL4 (R := R) :=
  (MulEquiv.subgroupCongr
    (elementaryGroup_eq_top L hdiv hdiag 4 (by omega))).trans
    Subgroup.topEquiv

/-- Full upper-left block stabilization before restricting the source to
`EL₃`. -/
noncomputable def fullCoreEmbedding : GL3 (R := R) →* GL4 (R := R) :=
  (elementaryReindexUnitEquiv (R := R)
      RankFour.stabilizationIndexEquiv).toMonoidHom.comp
    (stabilizeUnit (R := R) (ι := Fin 3) (κ := Unit))

private theorem elementaryEquivGL4_comp_coreEmbedding
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R) :
    (elementaryEquivGL4 L hdiv hdiag).toMonoidHom.comp
        (RankFour.coreEmbedding (A := R)) =
      (fullCoreEmbedding (R := R)).comp
        (elementaryGroup (Fin 3) R).subtype := by
  ext g
  rfl

@[simp] private theorem stabilizationIndexEquiv_last :
    RankFour.stabilizationIndexEquiv (Sum.inr ()) = (3 : Fin 4) := rfl

/-- Under `GL₃ = EL₃` and `GL₄ = EL₄`, the stabilized elementary core is
exactly the intrinsic last-coordinate block. -/
theorem coreRange_map_eq_coordinateBlock
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R) :
    (RankFourGlobalization.coreRange (R := R)).map
        (elementaryEquivGL4 L hdiv hdiag).toMonoidHom =
      coordinateBlock R (3 : Fin 4) := by
  rw [RankFourGlobalization.coreRange, MonoidHom.map_range]
  rw [elementaryEquivGL4_comp_coreEmbedding L hdiv hdiag,
    MonoidHom.range_comp, Subgroup.range_subtype,
    elementaryGroup_eq_top L hdiv hdiag 3 (by omega)]
  rw [← MonoidHom.range_eq_map]
  simpa only [fullCoreEmbedding, stabilizationIndexEquiv_last] using
    (range_reindexedStabilize_eq_coordinateBlock
      (R := R) RankFour.stabilizationIndexEquiv)

/-- **General rank-four theorem.**  Every ring with the four structural
hypotheses listed above has `(TT)/T` in elementary rank four. -/
theorem rankFour_hasTTmodT
    (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R) (hf : Function.Surjective f)
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R) :
    HasTTmodT.{0, v} (E4 (R := R)) := by
  have hT3small : HasKazhdanPropertyT.{0, 0} (E3 (R := R)) :=
    HasKazhdanPropertyT.of_surjective
      (elementaryGroupMap (ι := Fin 3) f)
      (elementaryGroupMap_surjective_of_surjective f hf)
      (FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT X)
  have hT3 : HasKazhdanPropertyT.{0, v} (E3 (R := R)) :=
    hT3small.liftUniverse
  have hT4 : HasKazhdanPropertyT.{0, v} (E4 (R := R)) :=
    L.rankFour_propertyT_of_rankThree hT3
  have h03 : HasRelativeTTmodT.{0, v} (E4 (R := R)) (X03 (R := R)) := by
    simpa only [FiniteTypeRankFourRelativeTT.X03,
      RankFourParabolicGeometry.X03] using
      (FiniteTypeRankFourRelativeTT.hasRelativeTTmodT_X03
        (R := R) X f hf)
  have h13 : HasRelativeTTmodT.{0, v} (E4 (R := R)) (X13 (R := R)) := by
    have h := h03.reindexRoot (Equiv.swap (0 : Fin 4) 1) 0 3 (by decide)
    simpa only [X13, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0)
        (by decide : (3 : Fin 4) ≠ 1)] using h
  have h23 : HasRelativeTTmodT.{0, v} (E4 (R := R)) (X23 (R := R)) := by
    have h := h03.reindexRoot (Equiv.swap (0 : Fin 4) 2) 0 3 (by decide)
    simpa only [X23, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0)
        (by decide : (3 : Fin 4) ≠ 2)] using h
  have h30 : HasRelativeTTmodT.{0, v} (E4 (R := R)) (X30 (R := R)) := by
    have h := h03.reindexRoot (Equiv.swap (0 : Fin 4) 3) 0 3 (by decide)
    simpa only [X30, Equiv.swap_apply_left, Equiv.swap_apply_right] using h
  have h31 : HasRelativeTTmodT.{0, v} (E4 (R := R)) (X31 (R := R)) := by
    let e : Equiv.Perm (Fin 4) :=
      (Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 1)
    have he0 : e 0 = 3 := by simp [e, Equiv.swap_apply_def]
    have he3 : e 3 = 1 := by simp [e]
    have h := h03.reindexRoot e 0 3 (by decide)
    simpa only [X31, he0, he3] using h
  have h32 : HasRelativeTTmodT.{0, v} (E4 (R := R)) (X32 (R := R)) := by
    let e : Equiv.Perm (Fin 4) :=
      (Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap (0 : Fin 4) 2)
    have he0 : e 0 = 3 := by simp [e, Equiv.swap_apply_def]
    have he3 : e 3 = 2 := by simp [e]
    have h := h03.reindexRoot e 0 3 (by decide)
    simpa only [X32, he0, he3] using h
  have hcore : HasRelativeTTmodT.{0, v} (E4 (R := R))
      (RankFourGlobalization.coreRange (R := R)) :=
    RankFourGlobalization.hasRelativeTTmodT_coreRange_of_roots
      hT4 h03 h13 h23 h30 h31 h32
  let e4 : E4 (R := R) ≃* GL4 (R := R) :=
    elementaryEquivGL4 L hdiv hdiag
  have hblock3 : HasRelativeTTmodT.{0, v} (GL4 (R := R))
      (coordinateBlock R (3 : Fin 4)) := by
    apply HasRelativeTTmodT.of_surjective e4.toMonoidHom e4.surjective
      (RankFourGlobalization.coreRange (R := R))
      (coordinateBlock R (3 : Fin 4))
    · rw [show e4 = elementaryEquivGL4 L hdiv hdiag from rfl,
        coreRange_map_eq_coordinateBlock L hdiv hdiag]
    · exact hcore
  have hblock : ∀ j : Fin 4,
      HasRelativeTTmodT.{0, v} (GL4 (R := R))
        (coordinateBlock R j) := by
    intro j
    by_cases hj : (3 : Fin 4) = j
    · subst j
      exact hblock3
    let e : Equiv.Perm (Fin 4) := Equiv.swap (3 : Fin 4) j
    have he : e 3 = j := by simp [e]
    apply HasRelativeTTmodT.of_surjective
      (elementaryReindexUnitEquiv (R := R) e).toMonoidHom
      (elementaryReindexUnitEquiv (R := R) e).surjective
      (coordinateBlock R (3 : Fin 4)) (coordinateBlock R j)
    · rw [coordinateBlock_map_reindex, he]
    · exact hblock3
  have hGL : HasTTmodT.{0, v} (GL4 (R := R)) :=
    hasTTmodT_of_relative_coordinateBlocks_of_sandwich
      (R := R) (ι := Fin 4) (by decide) hdiv hblock
  exact HasTTmodT.of_mulEquiv e4 hGL

/-- **General all-ranks theorem.**  Under the finite-presentation,
self-similarity, strong-division, and diagonal-class hypotheses, every
elementary rank `n ≥ 2` has property `(TT)/T`. -/
theorem elementaryGroup_hasTTmodT
    (X : Type) [Fintype X]
    (f : FreeAlgebra (ZMod 2) X →+* R) (hf : Function.Surjective f)
    (L : LeavittFamily R)
    (hdiv : HasSingleSandwichDivision R)
    (hdiag : HasElementaryDiagonalClass R)
    (n : ℕ) (hn : 2 ≤ n) :
    HasTTmodT.{0, v} (elementaryGroup (Fin n) R) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact HasTTmodT.of_mulEquiv
    (L.rankSuccEquiv m 3 (by omega) (by omega))
    (rankFour_hasTTmodT X f hf L hdiv hdiag)

end
end FiniteTypeLeavittTT
end GroupApproximation
