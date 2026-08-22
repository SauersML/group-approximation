import GroupApproximation.Sofic.BareDefectSource
import GroupApproximation.Sofic.FournierFacioUniversalGroup
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Algebra.HNNTorsionFree
import GroupApproximation.Algebra.HNNFinitePresentation
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-! The unconditional bare Fournier--Facio double-HNN source.  The auxiliary
factor is the explicit free group on two generators; simplicity is unused. -/

namespace GroupApproximation.FournierFacioDoubleHNNSource

open RealizationFromUniversalGroup
open scoped commutatorElement

variable (U : FournierFacioUniversal.UniversalKazhdanGroup)

abbrev FreeTwo := FreeGroup (Fin 2)
def freeLeft : FreeTwo := FreeGroup.of 0
def freeRight : FreeTwo := FreeGroup.of 1

def generatorPermutation (i : Fin 2) : Equiv.Perm (Fin 3) :=
  if i = 0 then Equiv.swap 0 1 else Equiv.swap 1 2

theorem free_commutator_ne_one : ⁅freeLeft, freeRight⁆ ≠ 1 := by
  intro h
  have himage := congrArg (FreeGroup.lift generatorPermutation) h
  have hperm : ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆ ≠ 1 := by
    decide
  apply hperm
  simpa [freeLeft, freeRight, generatorPermutation] using himage

theorem freeTwo_torsionFree : IsPowerTorsionFree FreeTwo :=
  IsPowerTorsionFree.of_isMulTorsionFree

abbrev TripleSource : Type := (U.Carrier × U.Carrier) × FreeTwo

theorem tripleSource_torsionFree : IsPowerTorsionFree (TripleSource U) :=
  (U.torsionFree.prod U.torsionFree).prod freeTwo_torsionFree

noncomputable def tripleEmbedding : TripleSource U →* U.Carrier :=
  Classical.choose (U.universal (TripleSource U) (tripleSource_torsionFree U))

theorem tripleEmbedding_injective : Function.Injective (tripleEmbedding U) :=
  Classical.choose_spec (U.universal (TripleSource U) (tripleSource_torsionFree U))

noncomputable def alphaOne : U.Carrier →* U.Carrier where
  toFun p := tripleEmbedding U ((p, 1), 1)
  map_one' := by simp
  map_mul' p q := by
    change tripleEmbedding U (((p, 1), 1) * ((q, 1), 1)) = _
    rw [map_mul]

noncomputable def alphaTwo : U.Carrier →* U.Carrier where
  toFun p := tripleEmbedding U ((1, p), 1)
  map_one' := by simp
  map_mul' p q := by
    change tripleEmbedding U (((1, p), 1) * ((1, q), 1)) = _
    rw [map_mul]

noncomputable def freeFactor : FreeTwo →* U.Carrier where
  toFun s := tripleEmbedding U ((1, 1), s)
  map_one' := by simp
  map_mul' s t := by
    change tripleEmbedding U (((1, 1), s) * ((1, 1), t)) = _
    rw [map_mul]

theorem alphaOne_injective : Function.Injective (alphaOne U) := fun _ _ h ↦
  congrArg (fun z : TripleSource U ↦ z.1.1) (tripleEmbedding_injective U h)

theorem alphaTwo_injective : Function.Injective (alphaTwo U) := fun _ _ h ↦
  congrArg (fun z : TripleSource U ↦ z.1.2) (tripleEmbedding_injective U h)

theorem freeFactor_injective : Function.Injective (freeFactor U) := fun _ _ h ↦
  congrArg (fun z : TripleSource U ↦ z.2) (tripleEmbedding_injective U h)

theorem freeFactor_commutes_alphaOne (s : FreeTwo) (p : U.Carrier) :
    Commute (freeFactor U s) (alphaOne U p) := by
  have h : Commute (((1, 1), s) : TripleSource U) ((p, 1), 1) := by
    rw [commute_iff_eq]; simp
  exact h.map (tripleEmbedding U)

theorem freeFactor_commutes_alphaTwo (s : FreeTwo) (p : U.Carrier) :
    Commute (freeFactor U s) (alphaTwo U p) := by
  have h : Commute (((1, 1), s) : TripleSource U) ((1, p), 1) := by
    rw [commute_iff_eq]; simp
  exact h.map (tripleEmbedding U)

theorem terminalRanges_disjoint : Disjoint (alphaOne U).range (alphaTwo U).range := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨p, hp⟩ ⟨q, hq⟩
  have h := tripleEmbedding_injective U (hp.trans hq.symm)
  have hp1 : p = 1 := congrArg (fun z : TripleSource U ↦ z.1.1) h
  rw [← hp, hp1, map_one]

noncomputable def firstEquiv : (⊤ : Subgroup U.Carrier) ≃* (alphaOne U).range :=
  (Subgroup.topEquiv).trans (MonoidHom.ofInjective (alphaOne_injective U))

@[simp] theorem coe_firstEquiv (p : U.Carrier) :
    (((firstEquiv U) ⟨p, Subgroup.mem_top p⟩ : (alphaOne U).range) : U.Carrier) =
      alphaOne U p := rfl

noncomputable abbrev FirstHNN :=
  HNNExtension U.Carrier ⊤ (alphaOne U).range (firstEquiv U)

theorem firstOf_injective :
    Function.Injective (HNNExtension.of : U.Carrier →* FirstHNN U) :=
  HNNExtension.of_injective (firstEquiv U)

theorem firstStable_compress (p : U.Carrier) :
    (HNNExtension.t : FirstHNN U) * HNNExtension.of p * HNNExtension.t⁻¹ =
      HNNExtension.of (alphaOne U p) := by
  have h := HNNExtension.equiv_eq_conj (φ := firstEquiv U) ⟨p, Subgroup.mem_top p⟩
  rw [coe_firstEquiv] at h
  exact h.symm

theorem firstHNN_torsionFree : IsPowerTorsionFree (FirstHNN U) :=
  HNNBritton.isPowerTorsionFree_hnn (firstEquiv U) U.torsionFree

theorem firstHNN_finitelyPresented : Group.IsFinitelyPresented (FirstHNN U) := by
  letI : Group.FG U.Carrier :=
    ProductFinitePresentation.fg_of_isFinitelyPresented U.Carrier
  letI : Group.FG ↑(⊤ : Subgroup U.Carrier) := Group.fg_of_surjective
    (f := (Subgroup.topEquiv (G := U.Carrier)).symm.toMonoidHom)
    (Subgroup.topEquiv (G := U.Carrier)).symm.surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension (firstEquiv U)

noncomputable def vertexInFirst : U.Carrier →* FirstHNN U := HNNExtension.of
noncomputable def secondTerminalInFirst : U.Carrier →* FirstHNN U :=
  (HNNExtension.of : U.Carrier →* FirstHNN U).comp (alphaTwo U)

theorem vertexInFirst_injective : Function.Injective (vertexInFirst U) := firstOf_injective U
theorem secondTerminalInFirst_injective : Function.Injective (secondTerminalInFirst U) :=
  (firstOf_injective U).comp (alphaTwo_injective U)

noncomputable def secondEquiv :
    (vertexInFirst U).range ≃* (secondTerminalInFirst U).range :=
  (MonoidHom.ofInjective (vertexInFirst_injective U)).symm.trans
    (MonoidHom.ofInjective (secondTerminalInFirst_injective U))

noncomputable abbrev DoubleHNN := HNNExtension (FirstHNN U) (vertexInFirst U).range
  (secondTerminalInFirst U).range (secondEquiv U)

theorem secondOf_injective :
    Function.Injective (HNNExtension.of : FirstHNN U →* DoubleHNN U) :=
  HNNExtension.of_injective (secondEquiv U)

noncomputable def vertexEmbedding : U.Carrier →* DoubleHNN U :=
  (HNNExtension.of : FirstHNN U →* DoubleHNN U).comp (vertexInFirst U)

theorem vertexEmbedding_injective : Function.Injective (vertexEmbedding U) :=
  (secondOf_injective U).comp (vertexInFirst_injective U)

@[simp] theorem coe_secondEquiv (p : U.Carrier) :
    (((secondEquiv U) ((MonoidHom.ofInjective (vertexInFirst_injective U)) p) :
      (secondTerminalInFirst U).range) : FirstHNN U) = secondTerminalInFirst U p := by
  show (((((MonoidHom.ofInjective (vertexInFirst_injective U)).symm.trans
    (MonoidHom.ofInjective (secondTerminalInFirst_injective U)))
    ((MonoidHom.ofInjective (vertexInFirst_injective U)) p) :
      (secondTerminalInFirst U).range) : FirstHNN U) = _)
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply]

theorem secondStable_compress (p : U.Carrier) :
    (HNNExtension.t : DoubleHNN U) * vertexEmbedding U p * HNNExtension.t⁻¹ =
      vertexEmbedding U (alphaTwo U p) := by
  have h := HNNExtension.equiv_eq_conj (φ := secondEquiv U)
    ((MonoidHom.ofInjective (vertexInFirst_injective U)) p)
  rw [coe_secondEquiv] at h
  exact h.symm

theorem firstStable_compress_double (p : U.Carrier) :
    HNNExtension.of (HNNExtension.t : FirstHNN U) * vertexEmbedding U p *
      (HNNExtension.of (HNNExtension.t : FirstHNN U) : DoubleHNN U)⁻¹ =
        vertexEmbedding U (alphaOne U p) := by
  simpa using congrArg (HNNExtension.of : FirstHNN U →* DoubleHNN U)
    (firstStable_compress U p)

theorem doubleHNN_torsionFree : IsPowerTorsionFree (DoubleHNN U) :=
  HNNBritton.isPowerTorsionFree_hnn (secondEquiv U) (firstHNN_torsionFree U)

theorem doubleHNN_finitelyPresented : Group.IsFinitelyPresented (DoubleHNN U) := by
  letI : Group.IsFinitelyPresented (FirstHNN U) := firstHNN_finitelyPresented U
  letI : Group.FG U.Carrier := ProductFinitePresentation.fg_of_isFinitelyPresented U.Carrier
  let e : U.Carrier ≃* (vertexInFirst U).range :=
    MonoidHom.ofInjective (vertexInFirst_injective U)
  letI : Group.FG (vertexInFirst U).range :=
    Group.fg_of_surjective e.toMonoidHom e.surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension (secondEquiv U)

noncomputable def freeIntoDouble : FreeTwo →* DoubleHNN U :=
  (vertexEmbedding U).comp (freeFactor U)

theorem freeIntoDouble_injective : Function.Injective (freeIntoDouble U) :=
  (vertexEmbedding_injective U).comp (freeFactor_injective U)

theorem freeDouble_commutes_firstCompression (p : U.Carrier) :
    Commute (freeIntoDouble U freeLeft)
      (HNNExtension.of (HNNExtension.t : FirstHNN U) * vertexEmbedding U p *
        (HNNExtension.of (HNNExtension.t : FirstHNN U) : DoubleHNN U)⁻¹) := by
  rw [firstStable_compress_double]
  exact (freeFactor_commutes_alphaOne U freeLeft p).map (vertexEmbedding U)

theorem freeDouble_commutator_ne_one :
    ⁅freeIntoDouble U freeLeft, freeIntoDouble U freeRight⁆ ≠ 1 := by
  intro h
  apply free_commutator_ne_one
  apply freeIntoDouble_injective U
  simpa only [map_commutatorElement, map_one] using h

noncomputable def witnessBase : U.Carrier := freeFactor U freeRight

noncomputable def defectData : BareDefectSourceData U.Carrier (DoubleHNN U) where
  iota := vertexEmbedding U
  u := HNNExtension.of (HNNExtension.t : FirstHNN U)
  s := freeIntoDouble U freeLeft
  kazhdan := U.kazhdan
  compresses := fun p ↦ ⟨alphaOne U p, firstStable_compress_double U p⟩
  commutesAfterCompression := freeDouble_commutes_firstCompression U
  witness := witnessBase U
  witness_commutator_ne_one := freeDouble_commutator_ne_one U

theorem terminalImages_disjoint_in_double :
    Disjoint ((vertexEmbedding U).comp (alphaOne U)).range
      ((vertexEmbedding U).comp (alphaTwo U)).range := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨p, hp⟩ ⟨q, hq⟩
  have hpq := vertexEmbedding_injective U (hp.trans hq.symm)
  have h := tripleEmbedding_injective U hpq
  have hp1 : p = 1 := congrArg (fun z : TripleSource U ↦ z.1.1) h
  rw [← hp, hp1, map_one, map_one]

theorem defectData_package :
    IsPowerTorsionFree (DoubleHNN U) ∧ Group.IsFinitelyPresented (DoubleHNN U) ∧
      Nonempty (BareDefectSourceData U.Carrier (DoubleHNN U)) :=
  ⟨doubleHNN_torsionFree U, doubleHNN_finitelyPresented U, ⟨defectData U⟩⟩

end GroupApproximation.FournierFacioDoubleHNNSource
