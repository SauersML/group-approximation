import GroupApproximation.Higman.OmegaHalfLineFiniteCutter

/-!
# The target cutter for one-sided Omega insertion

The source cutter uses labels `bK l` with `l` supported on the right tail.  For
a selected block `beta`, the target uses the genuinely different label set
`bK (beta + l)`.  This file gives that target its own adapted integer row and
finite Row cutter.  It then restricts both source and target witness embeddings
to the same abstract free group on `RightTailIndex m`; no extension of
`l \mapsto beta + l` to an automorphism of the entire conjugator alphabet is
asserted or needed for these range data.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The conjugator labels obtained after prepending `beta` to a right-tail
sequence. -/
noncomputable def insertedRightTailLabel (m : ℕ) (beta : E) : Set ↥Conj.K :=
  bK '' ((fun l : E => beta + l) '' rightTailSeq m)

/-- An explicit infinite family of inserted right-tail labels. -/
noncomputable def insertedRightTailLabelNat (m : ℕ) (beta : E) (n : ℕ) :
    ↥(insertedRightTailLabel m beta) :=
  ⟨bK (beta + Finsupp.single (m : ℤ) ((n : ℤ) + 1)), by
    refine ⟨beta + Finsupp.single (m : ℤ) ((n : ℤ) + 1), ?_, rfl⟩
    refine ⟨Finsupp.single (m : ℤ) ((n : ℤ) + 1), ?_, rfl⟩
    intro i hi
    have him : i = (m : ℤ) := by
      by_contra him
      exact hi (by simp [him])
    omega⟩

theorem insertedRightTailLabelNat_injective (m : ℕ) (beta : E) :
    Function.Injective (insertedRightTailLabelNat m beta) := by
  intro n k hnk
  have hb :
      bK (beta + Finsupp.single (m : ℤ) ((n : ℤ) + 1)) =
        bK (beta + Finsupp.single (m : ℤ) ((k : ℤ) + 1)) :=
    congrArg Subtype.val hnk
  have hs := add_left_cancel (bK_injective hb)
  have hv := congrArg (fun f : E => f (m : ℤ)) hs
  simp only [Finsupp.single_eq_same] at hv
  omega

noncomputable instance insertedRightTailLabel_infinite (m : ℕ) (beta : E) :
    Infinite ↥(insertedRightTailLabel m beta) :=
  Infinite.of_injective (insertedRightTailLabelNat m beta)
    (insertedRightTailLabelNat_injective m beta)

/-- Labels obtained by inserting a nonzero coordinate immediately to the
left of the tail are outside the inserted target label set. -/
noncomputable def outsideInsertedRightTailLabelNat
    (m : ℕ) (beta : E) (n : ℕ) :
    ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) :=
  ⟨bK (beta + Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1)), by
    rintro ⟨l, ⟨r, hr, rfl⟩, heq⟩
    have hs : beta + r =
        beta + Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1) :=
      bK_injective heq
    have hr_eq : r =
        Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1) :=
      add_left_cancel hs
    have hnz : ((n : ℤ) + 1) ≠ 0 := by omega
    have hsupport : r ((m : ℤ) - 1) ≠ 0 := by
      rw [hr_eq]
      simpa using hnz
    have := hr ((m : ℤ) - 1) hsupport
    omega⟩

theorem outsideInsertedRightTailLabelNat_injective (m : ℕ) (beta : E) :
    Function.Injective (outsideInsertedRightTailLabelNat m beta) := by
  intro n k hnk
  have hb :
      bK (beta + Finsupp.single ((m : ℤ) - 1) ((n : ℤ) + 1)) =
        bK (beta + Finsupp.single ((m : ℤ) - 1) ((k : ℤ) + 1)) :=
    congrArg Subtype.val hnk
  have hs := add_left_cancel (bK_injective hb)
  have hv := congrArg (fun f : E => f ((m : ℤ) - 1)) hs
  simp only [Finsupp.single_eq_same] at hv
  omega

noncomputable instance outsideInsertedRightTailLabel_infinite
    (m : ℕ) (beta : E) :
    Infinite ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) :=
  Infinite.of_injective (outsideInsertedRightTailLabelNat m beta)
    (outsideInsertedRightTailLabelNat_injective m beta)

@[implicit_reducible] noncomputable def insertedRightTailLabelDenumerable
    (m : ℕ) (beta : E) : Denumerable ↥(insertedRightTailLabel m beta) :=
  Classical.choice (nonempty_denumerable ↥(insertedRightTailLabel m beta))

@[implicit_reducible] noncomputable def outsideInsertedRightTailLabelDenumerable
    (m : ℕ) (beta : E) :
    Denumerable ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) :=
  Classical.choice
    (nonempty_denumerable
      ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K))

/-- An integer enumeration adapted exactly to the inserted target labels. -/
noncomputable def insertedRightTailLabelEquivInt
    (m : ℕ) (beta : E) : ↥Conj.K ≃ ℤ := by
  classical
  letI : Denumerable ↥(insertedRightTailLabel m beta) :=
    insertedRightTailLabelDenumerable m beta
  letI : Denumerable ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) :=
    outsideInsertedRightTailLabelDenumerable m beta
  exact (Equiv.Set.sumCompl (insertedRightTailLabel m beta)).symm |>.trans
    ((Denumerable.eqv _).sumCongr (Denumerable.eqv _)) |>.trans
    Equiv.intEquivNatSumNat.symm

theorem insertedRightTailLabelEquivInt_nonneg_iff
    (m : ℕ) (beta : E) (q : ↥Conj.K) :
    0 ≤ insertedRightTailLabelEquivInt m beta q ↔
      q ∈ insertedRightTailLabel m beta := by
  classical
  letI : Denumerable ↥(insertedRightTailLabel m beta) :=
    insertedRightTailLabelDenumerable m beta
  letI : Denumerable ↥((insertedRightTailLabel m beta)ᶜ : Set ↥Conj.K) :=
    outsideInsertedRightTailLabelDenumerable m beta
  by_cases hq : q ∈ insertedRightTailLabel m beta
  · simp only [insertedRightTailLabelEquivInt, Equiv.trans_apply,
      Equiv.Set.sumCompl_symm_apply_of_mem hq, Equiv.sumCongr_apply]
    constructor
    · intro
      exact hq
    · intro
      change 0 ≤ Int.ofNat _
      exact Int.natCast_nonneg _
  · simp only [insertedRightTailLabelEquivInt, Equiv.trans_apply,
      Equiv.Set.sumCompl_symm_apply_of_notMem hq, Equiv.sumCongr_apply]
    constructor
    · intro hnonneg
      change 0 ≤ Int.negSucc _ at hnonneg
      omega
    · exact False.elim ∘ hq

noncomputable def insertedRightTailFreeEquiv (m : ℕ) (beta : E) :
    FreeGroup ↥Conj.K ≃* FreeGroup ℤ :=
  FreeGroup.freeGroupCongr (insertedRightTailLabelEquivInt m beta)

@[simp] theorem insertedRightTailFreeEquiv_of
    (m : ℕ) (beta : E) (q : ↥Conj.K) :
    insertedRightTailFreeEquiv m beta (FreeGroup.of q) =
      FreeGroup.of (insertedRightTailLabelEquivInt m beta q) := rfl

noncomputable def insertedRightTailRowHom (m : ℕ) (beta : E) :
    FreeGroup ↥Conj.K →* Row.F₀ :=
  Row.basisHom.comp (insertedRightTailFreeEquiv m beta).toMonoidHom

theorem insertedRightTailRowHom_injective (m : ℕ) (beta : E) :
    Function.Injective (insertedRightTailRowHom m beta) :=
  Row.basisHom_injective.comp (insertedRightTailFreeEquiv m beta).injective

@[simp] theorem insertedRightTailRowHom_of
    (m : ℕ) (beta : E) (q : ↥Conj.K) :
    insertedRightTailRowHom m beta (FreeGroup.of q) =
      Row.row (insertedRightTailLabelEquivInt m beta q) := by
  rw [insertedRightTailRowHom, MonoidHom.comp_apply]
  change Row.basisHom
    (insertedRightTailFreeEquiv m beta (FreeGroup.of q)) = _
  rw [insertedRightTailFreeEquiv_of, Row.basisHom_of]

theorem map_insertedRightTailCoord_insertedRightTailRowHom
    (m : ℕ) (beta : E) :
    (Star.coordSub (insertedRightTailLabel m beta)).map
        (insertedRightTailRowHom m beta) = Row.HalfRow := by
  unfold Star.coordSub
  rw [MonoidHom.map_closure, Row.halfRow_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨insertedRightTailLabelEquivInt m beta q,
      (insertedRightTailLabelEquivInt_nonneg_iff m beta q).mpr hq,
      (insertedRightTailRowHom_of m beta q).symm⟩
  · rintro ⟨i, hi, rfl⟩
    let q : ↥Conj.K := (insertedRightTailLabelEquivInt m beta).symm i
    have hq : q ∈ insertedRightTailLabel m beta :=
      (insertedRightTailLabelEquivInt_nonneg_iff m beta q).mp (by
        simpa [q] using hi)
    exact ⟨FreeGroup.of q, ⟨q, hq, rfl⟩, by simp [q]⟩

noncomputable def insertedRightTailLabelOvergroup (m : ℕ) (beta : E) :
    TorsionFreeFPOvergroup (FreeGroup ↥Conj.K) where
  K := Row.F₀
  torsionFree := IsPowerTorsionFree.of_isMulTorsionFree
  emb := insertedRightTailRowHom m beta
  emb_injective := insertedRightTailRowHom_injective m beta

theorem benignTF_insertedRightTailCoord (m : ℕ) (beta : E) :
    BenignTF (Star.coordSub (insertedRightTailLabel m beta)) := by
  have h := BenignTF.comap (insertedRightTailLabelOvergroup m beta)
    (insertedRightTailRowHom m beta) Row.benignTF_halfRow
  have hcomap : Row.HalfRow.comap (insertedRightTailRowHom m beta) =
      Star.coordSub (insertedRightTailLabel m beta) := by
    rw [← map_insertedRightTailCoord_insertedRightTailRowHom m beta]
    exact Subgroup.comap_map_eq_self_of_injective
      (insertedRightTailRowHom_injective m beta) _
  rwa [hcomap] at h

noncomputable def insertedRightTailCoordWitness (m : ℕ) (beta : E) :
    TorsionFreeBenignWitness
      (Star.coordSub (insertedRightTailLabel m beta)) :=
  Classical.choice (benignTF_insertedRightTailCoord m beta)

/-- Target counterpart of the source paired product witness. -/
noncomputable def insertedRightTailPairedProductWitnessRaw
    (m : ℕ) (beta : E) :
    TorsionFreeBenignWitness
      ((⊤ : Subgroup (FreeGroup ↥Conj.K)) ⊓
        Star.coordSub (insertedRightTailLabel m beta)) :=
  pairedGraphTopWitness.inf (insertedRightTailCoordWitness m beta)

/-- Restrict the finite source witness embedding to the common abstract
right-tail free group. -/
noncomputable def rightTailAbstractSourceInCutter (m : ℕ) :
    FreeGroup (RightTailIndex m) →*
      (rightTailPairedProductWitnessRaw m).witness.K :=
  (rightTailPairedProductWitnessRaw m).witness.emb.comp
    (FreeGroup.map (rightTailIndexToK m))

/-- Restrict the finite target witness embedding to the same abstract free
group, now using the inserted labels. -/
noncomputable def rightTailAbstractTargetInCutter (m : ℕ) (beta : E) :
    FreeGroup (RightTailIndex m) →*
      (insertedRightTailPairedProductWitnessRaw m beta).witness.K :=
  (insertedRightTailPairedProductWitnessRaw m beta).witness.emb.comp
    (FreeGroup.map (insertedRightTailIndexToK m beta))

theorem rightTailAbstractSourceInCutter_injective (m : ℕ) :
    Function.Injective (rightTailAbstractSourceInCutter m) :=
  (rightTailPairedProductWitnessRaw m).witness.emb_injective.comp
    (FreeGroup.map_injective (rightTailIndexToK_injective m))

theorem rightTailAbstractTargetInCutter_injective (m : ℕ) (beta : E) :
    Function.Injective (rightTailAbstractTargetInCutter m beta) :=
  (insertedRightTailPairedProductWitnessRaw m beta).witness.emb_injective.comp
    (FreeGroup.map_injective (insertedRightTailIndexToK_injective m beta))

/-- The source and target restricted ranges are canonically isomorphic by
evaluating the same word in the common abstract right-tail basis. -/
noncomputable def rightTailAbstractRangeEquiv (m : ℕ) (beta : E) :
    (rightTailAbstractSourceInCutter m).range ≃*
      (rightTailAbstractTargetInCutter m beta).range := by
  rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map]
  exact
    (Subgroup.equivMapOfInjective ⊤ (rightTailAbstractSourceInCutter m)
        (rightTailAbstractSourceInCutter_injective m)).symm.trans
      (Subgroup.equivMapOfInjective ⊤
        (rightTailAbstractTargetInCutter m beta)
        (rightTailAbstractTargetInCutter_injective m beta))

end Omega
end Higman
end GroupApproximation
