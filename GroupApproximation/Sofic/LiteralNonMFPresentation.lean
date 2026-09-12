import GroupApproximation.Algebra.PresentedGroupEvaluation
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.NormMFResidualDetector
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group

/-!
# The literal eight-generator presentation from the non-MF manuscript

This file encodes, without choosing a presentation cover, the group displayed
in Definition `def:E` of `non_mf_groups_exist.tex`.  Its generators are

`v1, v2, v3, x, y, z, t, c`,

so the advertised number of generators is indeed eight.  The first six
generators carry the twenty displayed base relators, `t` satisfies the six
displayed doubling relations, `c` is an involution centralising the base, and
the marked word is imposed to be central.  Its involution relation is derived
from these relations and is not imposed.

No completeness theorem for the six-generator base presentation is used in
this file.  This module asserts only the literal finite-presentation algebra;
the separate exact realization in `LiteralNonMFLinearWitness` proves that its
marked word is nontrivial.  The analytic endpoint is kept in a separate
module, so this presentation file makes no property-`(T)` or MF claim on its
own.
-/

namespace GroupApproximation
namespace LiteralNonMFPresentation

open scoped commutatorElement

noncomputable section

/-- Catch-all decidable equality for alphabets and free groups that have no
computable instance in scope.  It sits in the discrimination tree's catch-all
bucket, so any specific instance — `instDecidableEqFin` on the alphabets,
`FreeGroup.instDecidableEq` on the free groups — takes precedence over it.
The relator-count section at the end of this file depends on that: kernel
evaluation of a reduced-word normal form needs the computable instances. -/
local instance literalDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

instance literalFreeGroupCountable {α : Type*} [Countable α] :
    Countable (FreeGroup α) := by
  have hsurj : Function.Surjective (FreeGroup.mk : List (α × Bool) → _) := by
    intro g
    obtain ⟨L, hL⟩ := Quot.exists_rep g
    exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
  exact hsurj.countable

/-! ## The two finite alphabets -/

/-- The six base letters, ordered as `v1,v2,v3,x,y,z`. -/
abbrev BaseGenerator := Fin 6

/-- The final alphabet: six base letters followed by `t,c`. -/
abbrev Generator := BaseGenerator ⊕ Fin 2

abbrev v1Index : BaseGenerator := 0
abbrev v2Index : BaseGenerator := 1
abbrev v3Index : BaseGenerator := 2
abbrev xIndex : BaseGenerator := 3
abbrev yIndex : BaseGenerator := 4
abbrev zIndex : BaseGenerator := 5

abbrev Generator.base (i : BaseGenerator) : Generator := Sum.inl i
abbrev Generator.stable : Generator := Sum.inr 0
abbrev Generator.lamp : Generator := Sum.inr 1

theorem generator_card : Fintype.card Generator = 8 := by decide

/-- The printed ordering `v1,v2,v3,x,y,z,t,c` as the standard rank-eight
alphabet. -/
def generatorEquivFin8 : Generator ≃ Fin 8 :=
  finSumFinEquiv.trans (finCongr (by decide))

/-! ## Free words -/

abbrev bv1 : FreeGroup BaseGenerator := FreeGroup.of v1Index
abbrev bv2 : FreeGroup BaseGenerator := FreeGroup.of v2Index
abbrev bv3 : FreeGroup BaseGenerator := FreeGroup.of v3Index
abbrev bx : FreeGroup BaseGenerator := FreeGroup.of xIndex
abbrev bY : FreeGroup BaseGenerator := FreeGroup.of yIndex
abbrev bz : FreeGroup BaseGenerator := FreeGroup.of zIndex

abbrev vertexLetter (i : BaseGenerator) : FreeGroup Generator :=
  FreeGroup.of (Generator.base i)

abbrev v1Word : FreeGroup Generator := vertexLetter v1Index
abbrev v2Word : FreeGroup Generator := vertexLetter v2Index
abbrev v3Word : FreeGroup Generator := vertexLetter v3Index
abbrev xWord : FreeGroup Generator := vertexLetter xIndex
abbrev yWord : FreeGroup Generator := vertexLetter yIndex
abbrev zWord : FreeGroup Generator := vertexLetter zIndex
abbrev stableWord : FreeGroup Generator := FreeGroup.of Generator.stable
abbrev lampWord : FreeGroup Generator := FreeGroup.of Generator.lamp

/-- Commutator word, with the manuscript convention `[g,h]=ghg⁻¹h⁻¹`. -/
def commutatorWord {G : Type*} [Group G] (g h : G) : G :=
  g * h * g⁻¹ * h⁻¹

/-- Homomorphisms evaluate the raw commutator word as the intrinsic group
commutator. -/
theorem map_commutatorWord {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g h : G) :
    f (commutatorWord g h) = ⁅f g, f h⁆ := by
  simp [commutatorWord, commutatorElement_def]

/-- Embed words in the six base letters into the final alphabet. -/
def embedBaseWord : FreeGroup BaseGenerator →* FreeGroup Generator :=
  FreeGroup.lift (fun i ↦ vertexLetter i)

/-! ## The twenty literal base relators -/

abbrev baseRelXCube : FreeGroup BaseGenerator := bx ^ 3
abbrev baseRelYCube : FreeGroup BaseGenerator := bY ^ 3
abbrev baseRelZSq : FreeGroup BaseGenerator := bz ^ 2
abbrev baseRelXZCube : FreeGroup BaseGenerator := (bx * bz) ^ 3
abbrev baseRelYZCube : FreeGroup BaseGenerator := (bY * bz) ^ 3
abbrev baseRelXInvZXY : FreeGroup BaseGenerator := (bx⁻¹ * bz * bx * bY) ^ 2
abbrev baseRelYInvZYX : FreeGroup BaseGenerator := (bY⁻¹ * bz * bY * bx) ^ 2
abbrev baseRelXYSix : FreeGroup BaseGenerator := (bx * bY) ^ 6

abbrev baseRelV12 : FreeGroup BaseGenerator := commutatorWord bv1 bv2
abbrev baseRelV13 : FreeGroup BaseGenerator := commutatorWord bv1 bv3
abbrev baseRelV23 : FreeGroup BaseGenerator := commutatorWord bv2 bv3

abbrev baseRelXV1 : FreeGroup BaseGenerator := bx * bv1 * bx⁻¹ * bv3⁻¹
abbrev baseRelXV2 : FreeGroup BaseGenerator := bx * bv2 * bx⁻¹ * bv1⁻¹
abbrev baseRelXV3 : FreeGroup BaseGenerator := bx * bv3 * bx⁻¹ * bv2⁻¹
abbrev baseRelYV1 : FreeGroup BaseGenerator := bY * bv1 * bY⁻¹ * bv1⁻¹
abbrev baseRelYV2 : FreeGroup BaseGenerator :=
  bY * bv2 * bY⁻¹ * (bv2⁻¹ * bv3)⁻¹
abbrev baseRelYV3 : FreeGroup BaseGenerator :=
  bY * bv3 * bY⁻¹ * (bv1 * bv2⁻¹)⁻¹
abbrev baseRelZV1 : FreeGroup BaseGenerator :=
  bz * bv1 * bz⁻¹ * (bv2 * bv3⁻¹)⁻¹
abbrev baseRelZV2 : FreeGroup BaseGenerator :=
  bz * bv2 * bz⁻¹ * (bv1 * bv3⁻¹)⁻¹
abbrev baseRelZV3 : FreeGroup BaseGenerator :=
  bz * bv3 * bz⁻¹ * (bv3⁻¹)⁻¹

/-- Exactly the twenty relators displayed in `eq:gamma-presentation`. -/
noncomputable def baseRelators : Finset (FreeGroup BaseGenerator) :=
  [baseRelXCube, baseRelYCube, baseRelZSq, baseRelXZCube,
   baseRelYZCube, baseRelXInvZXY, baseRelYInvZYX, baseRelXYSix,
   baseRelV12, baseRelV13, baseRelV23,
   baseRelXV1, baseRelXV2, baseRelXV3,
   baseRelYV1, baseRelYV2, baseRelYV3,
   baseRelZV1, baseRelZV2, baseRelZV3].toFinset

/-- Stable, decidability-independent membership interface for the twenty
displayed base relators. -/
theorem mem_baseRelators_iff (r : FreeGroup BaseGenerator) :
    r ∈ baseRelators ↔
      r = baseRelXCube ∨ r = baseRelYCube ∨ r = baseRelZSq ∨
      r = baseRelXZCube ∨ r = baseRelYZCube ∨
      r = baseRelXInvZXY ∨ r = baseRelYInvZYX ∨
      r = baseRelXYSix ∨ r = baseRelV12 ∨ r = baseRelV13 ∨
      r = baseRelV23 ∨ r = baseRelXV1 ∨ r = baseRelXV2 ∨
      r = baseRelXV3 ∨ r = baseRelYV1 ∨ r = baseRelYV2 ∨
      r = baseRelYV3 ∨ r = baseRelZV1 ∨ r = baseRelZV2 ∨
      r = baseRelZV3 := by
  simp [baseRelators]

/-- The literal six-generator base group. -/
noncomputable abbrev Base : Type :=
  PresentedGroup ((baseRelators : Finset (FreeGroup BaseGenerator)) :
    Set (FreeGroup BaseGenerator))

instance base_finitelyPresented : Group.IsFinitelyPresented Base := inferInstance

noncomputable instance base_countable : Countable Base :=
  (PresentedGroup.mk_surjective
    ((baseRelators : Finset (FreeGroup BaseGenerator)) :
      Set (FreeGroup BaseGenerator))).countable

/-! ## The remaining displayed relators -/

/-- The right-hand side of the stable-letter relation, before embedding it
in the final alphabet. -/
def compressedBaseWord (i : BaseGenerator) : FreeGroup BaseGenerator :=
  if i = v1Index then bv1 ^ 2
  else if i = v2Index then bv2 ^ 2
  else if i = v3Index then bv3 ^ 2
  else if i = xIndex then bx
  else if i = yIndex then bY
  else bz

/-- The right-hand side of the stable-letter relation for a base generator. -/
def compressedGeneratorWord (i : BaseGenerator) : FreeGroup Generator :=
  embedBaseWord (compressedBaseWord i)

/-- `t s t⁻¹ = compressedGeneratorWord s`. -/
def stableRelator (i : BaseGenerator) : FreeGroup Generator :=
  stableWord * vertexLetter i * stableWord⁻¹ * (compressedGeneratorWord i)⁻¹

/-- The conjugated lamp `d=tct⁻¹`. -/
abbrev displacedLampWord : FreeGroup Generator :=
  stableWord * lampWord * stableWord⁻¹

/-- The literal marked word `[d,v₁dv₁⁻¹]`. -/
abbrev markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (v1Word * displacedLampWord * v1Word⁻¹)

noncomputable def transportedBaseRelators : Finset (FreeGroup Generator) :=
  baseRelators.image embedBaseWord

noncomputable def stableRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image stableRelator

noncomputable def lampRelators : Finset (FreeGroup Generator) :=
  {lampWord ^ 2} ∪
    Finset.univ.image (fun i : BaseGenerator ↦
      commutatorWord lampWord (vertexLetter i))

noncomputable def markedRelators : Finset (FreeGroup Generator) :=
  Finset.univ.image (fun i : Generator ↦
    commutatorWord markedWord (FreeGroup.of i))

/-- All relators in the literal eight-generator presentation. -/
noncomputable def relators : Finset (FreeGroup Generator) :=
  transportedBaseRelators ∪ stableRelators ∪ lampRelators ∪ markedRelators

/-- The literal group `E` printed in Definition `def:E`. -/
noncomputable abbrev MarkedGroup : Type :=
  PresentedGroup ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

instance markedGroup_finitelyPresented : Group.IsFinitelyPresented MarkedGroup :=
  inferInstance

noncomputable instance markedGroup_countable : Countable MarkedGroup :=
  (PresentedGroup.mk_surjective
    ((relators : Finset (FreeGroup Generator)) :
      Set (FreeGroup Generator))).countable

noncomputable abbrev wordInMarkedGroup : FreeGroup Generator →* MarkedGroup :=
  PresentedGroup.mk ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

noncomputable abbrev v1 : MarkedGroup := wordInMarkedGroup v1Word
noncomputable abbrev v2 : MarkedGroup := wordInMarkedGroup v2Word
noncomputable abbrev v3 : MarkedGroup := wordInMarkedGroup v3Word
noncomputable abbrev x : MarkedGroup := wordInMarkedGroup xWord
noncomputable abbrev y : MarkedGroup := wordInMarkedGroup yWord
noncomputable abbrev z : MarkedGroup := wordInMarkedGroup zWord
noncomputable abbrev stable : MarkedGroup := wordInMarkedGroup stableWord
noncomputable abbrev lamp : MarkedGroup := wordInMarkedGroup lampWord
noncomputable abbrev mark : MarkedGroup := wordInMarkedGroup markedWord

/-! ## Free-word evaluation helpers -/

/-- The universal map from a presented group computes by free evaluation on
every represented word. -/
theorem presentedToGroup_mk {X M : Type*} [Group M]
    {R : Set (FreeGroup X)} {f : X → M}
    (h : ∀ r ∈ R, FreeGroup.lift f r = 1)
    (w : FreeGroup X) :
    PresentedGroup.toGroup h (PresentedGroup.mk R w) =
      FreeGroup.lift f w := by
  refine freeGroup_hom_eq_on_generators
    (f := (PresentedGroup.toGroup h).comp (PresentedGroup.mk R))
    (g := FreeGroup.lift f) ?_ w
  intro i
  rw [MonoidHom.comp_apply,
    show PresentedGroup.mk R (FreeGroup.of i) =
      PresentedGroup.of i from rfl,
    PresentedGroup.toGroup.of, FreeGroup.lift_apply_of]

theorem lift_embedBaseWord {M : Type*} [Group M]
    (f : Generator → M) (w : FreeGroup BaseGenerator) :
    FreeGroup.lift f (embedBaseWord w) =
      FreeGroup.lift (fun i ↦ f (Generator.base i)) w := by
  change ((FreeGroup.lift f).comp embedBaseWord) w = _
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [embedBaseWord]

/-! ## The canonical base homomorphism and the compression inclusion -/

/-- The canonical map from the literal six-generator base into `E`. -/
noncomputable def baseMap : Base →* MarkedGroup := by
  apply PresentedGroup.toGroup
    (f := fun i : BaseGenerator ↦ wordInMarkedGroup (vertexLetter i))
  intro r hr
  rw [← lift_embedBaseWord
    (f := fun j : Generator ↦ wordInMarkedGroup (FreeGroup.of j))]
  rw [freeGroup_lift_presentedGroup_generators]
  apply PresentedGroup.one_of_mem
  change embedBaseWord r ∈ relators
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl
    (Finset.mem_image.mpr ⟨r, Finset.mem_coe.mp hr, rfl⟩)))

@[simp] theorem baseMap_generator (i : BaseGenerator) :
    baseMap (PresentedGroup.of i) = wordInMarkedGroup (vertexLetter i) := by
  exact PresentedGroup.toGroup.of _

theorem baseMap_mk (w : FreeGroup BaseGenerator) :
    baseMap (PresentedGroup.mk _ w) =
      wordInMarkedGroup (embedBaseWord w) := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ w) = _
  rw [presentedToGroup_mk]
  rw [← lift_embedBaseWord
    (f := fun j : Generator ↦ wordInMarkedGroup (FreeGroup.of j))]
  rw [freeGroup_lift_presentedGroup_generators]

/-- Each displayed stable relation holds in the presented group. -/
theorem stable_relation (i : BaseGenerator) :
    stable * baseMap (PresentedGroup.of i) * stable⁻¹ =
      wordInMarkedGroup (compressedGeneratorWord i) := by
  have hrel : wordInMarkedGroup (stableRelator i) = 1 := by
    apply PresentedGroup.one_of_mem
    change stableRelator i ∈ relators
    simp only [relators, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))
  simp only [stableRelator, map_mul, map_inv] at hrel
  exact mul_inv_eq_one.mp hrel

/-- Conjugation by `t` sends the entire image of the literal base back into
that image.  This uses only the six displayed stable relations. -/
theorem stable_conjugates_base_into_base :
    ∀ g : Base, stable * baseMap g * stable⁻¹ ∈ baseMap.range := by
  intro g
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      rw [show PresentedGroup.mk _ (FreeGroup.of i) =
        PresentedGroup.of i from rfl]
      rw [stable_relation]
      exact ⟨PresentedGroup.mk _ (compressedBaseWord i), baseMap_mk _⟩
  | inv_of i hi =>
      have hinv := baseMap.range.inv_mem hi
      rw [map_inv]
      have heq :
          stable * (baseMap (PresentedGroup.mk _ (FreeGroup.of i)))⁻¹ *
              stable⁻¹ =
            (stable * baseMap (PresentedGroup.mk _ (FreeGroup.of i)) *
              stable⁻¹)⁻¹ := by group
      exact (congrArg (fun q : MarkedGroup ↦ q ∈ baseMap.range) heq).mpr hinv
  | mul a b ha hb =>
      rw [map_mul]
      rw [map_mul baseMap]
      have hmul := baseMap.range.mul_mem ha hb
      have heq :
          stable *
              (baseMap (PresentedGroup.mk _ a) *
                baseMap (PresentedGroup.mk _ b)) * stable⁻¹ =
            (stable * baseMap (PresentedGroup.mk _ a) * stable⁻¹) *
              (stable * baseMap (PresentedGroup.mk _ b) * stable⁻¹) := by
        group
      exact (congrArg (fun q : MarkedGroup ↦ q ∈ baseMap.range) heq).mpr hmul

/-! ## Centrality relations -/

theorem lamp_commutes_base_generator (i : BaseGenerator) :
    Commute lamp (baseMap (PresentedGroup.of i)) := by
  rw [baseMap_generator]
  have hcomm : wordInMarkedGroup
      (commutatorWord lampWord (vertexLetter i)) = 1 := by
    apply PresentedGroup.one_of_mem
    change commutatorWord lampWord (vertexLetter i) ∈ relators
    simp [relators, lampRelators]
  rw [map_commutatorWord] at hcomm
  exact commutatorElement_eq_one_iff_commute.mp hcomm

theorem lamp_commutes_base (g : Base) : Commute lamp (baseMap g) := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_right _
  | of i =>
      rw [show PresentedGroup.mk _ (FreeGroup.of i) =
        PresentedGroup.of i from rfl]
      exact lamp_commutes_base_generator i
  | inv_of i hi =>
      rw [map_inv]
      exact hi.inv_right
  | mul a b ha hb =>
      simpa only [map_mul] using ha.mul_right hb

theorem lamp_sq : lamp ^ 2 = 1 := by
  apply PresentedGroup.one_of_mem
  change lampWord ^ 2 ∈ relators
  simp [relators, lampRelators]

theorem mark_central (g : MarkedGroup) : Commute mark g := by
  have hgen : ∀ i : Generator,
      Commute mark (wordInMarkedGroup (FreeGroup.of i)) := by
    intro i
    have hcomm : wordInMarkedGroup
        (commutatorWord markedWord (FreeGroup.of i)) = 1 := by
      apply PresentedGroup.one_of_mem
      change commutatorWord markedWord (FreeGroup.of i) ∈ relators
      simp [relators, markedRelators]
    rw [map_commutatorWord] at hcomm
    exact commutatorElement_eq_one_iff_commute.mp hcomm
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_right _
  | of i => exact hgen i
  | inv_of i hi =>
      rw [map_inv]
      exact hi.inv_right
  | mul a b ha hb =>
      simpa only [map_mul] using ha.mul_right hb

/-- The literal marked element is the analytic marked-compression word. -/
theorem mark_eq_markedCompressionWord :
    mark = markedCompressionWord stable (baseMap (PresentedGroup.of v1Index))
      lamp := by
  simp only [mark, markedWord, markedCompressionWord, commutatorWord,
    displacedLampWord, v1Word, stable, lamp, map_mul, map_inv,
    baseMap_generator]
  group

/-- The marked involution relation is a consequence of centrality and of the
root-lamp involution relation; it is not a defining relator. -/
theorem mark_sq : mark ^ 2 = 1 := by
  rw [mark_eq_markedCompressionWord]
  exact markedCompressionWord_sq_eq_one_of_c_sq_of_central
    stable (baseMap (PresentedGroup.of v1Index)) lamp lamp_sq
    (fun g ↦ by
      rw [← mark_eq_markedCompressionWord]
      exact mark_central g)

/-! ## Exact-realization interface -/

/-- Data sufficient to evaluate every displayed relator in an arbitrary
group.  This is used by the separate matrix/telescope/Clifford witness. -/
structure Realization (M : Type*) [Group M] where
  baseGenerator : BaseGenerator → M
  stable : M
  lamp : M
  base_relations : ∀ r ∈ baseRelators,
    FreeGroup.lift baseGenerator r = 1
  stable_relations : ∀ i : BaseGenerator,
    stable * baseGenerator i * stable⁻¹ =
      FreeGroup.lift baseGenerator (compressedBaseWord i)
  lamp_sq : lamp ^ 2 = 1
  lamp_centralizes_base : ∀ i, Commute lamp (baseGenerator i)
  marked_central : ∀ g : M,
    Commute (markedCompressionWord stable (baseGenerator v1Index) lamp) g

def realizationGenerator {M : Type*} [Group M]
    (R : Realization M) : Generator → M
  | .inl i => R.baseGenerator i
  | .inr j => if j = 0 then R.stable else R.lamp

@[simp] theorem realizationGenerator_base {M : Type*} [Group M]
    (R : Realization M) (i : BaseGenerator) :
    realizationGenerator R (Generator.base i) = R.baseGenerator i := rfl

@[simp] theorem realizationGenerator_stable {M : Type*} [Group M]
    (R : Realization M) :
    realizationGenerator R Generator.stable = R.stable := by
  simp [realizationGenerator]

@[simp] theorem realizationGenerator_lamp {M : Type*} [Group M]
    (R : Realization M) :
    realizationGenerator R Generator.lamp = R.lamp := by
  simp [realizationGenerator]

theorem realization_eval_base {M : Type*} [Group M]
    (R : Realization M) (w : FreeGroup BaseGenerator) :
    FreeGroup.lift (realizationGenerator R) (embedBaseWord w) =
      FreeGroup.lift R.baseGenerator w := by
  rw [lift_embedBaseWord]
  rfl

@[simp] theorem realization_eval_compressed {M : Type*} [Group M]
    (R : Realization M) (i : BaseGenerator) :
    FreeGroup.lift (realizationGenerator R) (compressedGeneratorWord i) =
      FreeGroup.lift R.baseGenerator (compressedBaseWord i) := by
  exact realization_eval_base R (compressedBaseWord i)

@[simp] theorem realization_eval_marked {M : Type*} [Group M]
    (R : Realization M) :
    FreeGroup.lift (realizationGenerator R) markedWord =
      markedCompressionWord R.stable (R.baseGenerator v1Index) R.lamp := by
  simp [markedWord, markedCompressionWord, commutatorWord,
    displacedLampWord]
  group

/-- The universal homomorphism from the literal presentation to a
realization. -/
noncomputable def realizationHom {M : Type*} [Group M]
    (R : Realization M) : MarkedGroup →* M := by
  apply PresentedGroup.toGroup (f := realizationGenerator R)
  intro r hr
  change r ∈ relators at hr
  simp only [relators, Finset.mem_union] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    rw [realization_eval_base]
    exact R.base_relations q hq
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    simp only [stableRelator, map_mul, map_inv]
    rw [show FreeGroup.lift (realizationGenerator R) stableWord =
        R.stable by simp [stableWord],
      show FreeGroup.lift (realizationGenerator R) (vertexLetter i) =
        R.baseGenerator i by simp [vertexLetter],
      realization_eval_compressed]
    exact mul_inv_eq_one.mpr (R.stable_relations i)
  · simp only [lampRelators, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image] at hr
    rcases hr with rfl | ⟨i, -, rfl⟩
    · simpa using R.lamp_sq
    · rw [map_commutatorWord,
        show FreeGroup.lift (realizationGenerator R) lampWord =
          R.lamp by simp [lampWord],
        show FreeGroup.lift (realizationGenerator R) (vertexLetter i) =
          R.baseGenerator i by simp [vertexLetter]]
      exact commutatorElement_eq_one_iff_commute.mpr
        (R.lamp_centralizes_base i)
  · simp only [markedRelators, Finset.mem_image] at hr
    obtain ⟨i, -, rfl⟩ := hr
    rw [map_commutatorWord, realization_eval_marked,
      FreeGroup.lift_apply_of]
    exact commutatorElement_eq_one_iff_commute.mpr
      (R.marked_central (realizationGenerator R i))

@[simp] theorem realizationHom_base_generator {M : Type*} [Group M]
    (R : Realization M) (i : BaseGenerator) :
    realizationHom R (baseMap (PresentedGroup.of i)) = R.baseGenerator i := by
  rw [baseMap_generator]
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ (vertexLetter i)) = _
  rw [presentedToGroup_mk]
  simp [vertexLetter]

@[simp] theorem realizationHom_stable {M : Type*} [Group M]
    (R : Realization M) : realizationHom R stable = R.stable := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ stableWord) = _
  rw [presentedToGroup_mk]
  simp [stableWord]

@[simp] theorem realizationHom_lamp {M : Type*} [Group M]
    (R : Realization M) : realizationHom R lamp = R.lamp := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ lampWord) = _
  rw [presentedToGroup_mk]
  simp [lampWord]

@[simp] theorem realizationHom_mark {M : Type*} [Group M]
    (R : Realization M) :
    realizationHom R mark =
      markedCompressionWord R.stable (R.baseGenerator v1Index) R.lamp := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ markedWord) = _
  rw [presentedToGroup_mk, realization_eval_marked]

theorem mark_ne_one_of_realization {M : Type*} [Group M]
    (R : Realization M)
    (hR : markedCompressionWord R.stable (R.baseGenerator v1Index) R.lamp ≠ 1) :
    mark ≠ 1 := by
  intro h
  apply hR
  rw [← realizationHom_mark R, h, map_one]

/-- Everything about the literal presentation that is independent of its
Kazhdan theorem and its separating realization. -/
theorem literal_algebraic_package :
    Group.IsFinitelyPresented MarkedGroup ∧
      (∀ g : Base, stable * baseMap g * stable⁻¹ ∈ baseMap.range) ∧
      (∀ g : Base, Commute lamp (baseMap g)) ∧
      mark ^ 2 = 1 ∧
      (∀ g : MarkedGroup, Commute mark g) := by
  exact ⟨inferInstance, stable_conjugates_base_into_base,
    lamp_commutes_base, mark_sq, mark_central⟩

/-! ## Exact relator counts

The manuscript advertises twenty relators for the six-generator base and
forty-one relators for the displayed eight-generator presentation.  Both
numbers are properties of the finite *sets* `baseRelators` and `relators`,
not of the displayed lists, so they are genuine theorems: the printed words
have to be pairwise distinct in the relevant free group.

Everything above uses the classical `DecidableEq` instance, under which no
`Finset` cardinality computes.  The section below therefore switches that
instance off, re-presents each relator family as an explicit `List`, and
proves the lists duplicate free by kernel evaluation of the reduced-word
normal form.  The counts are then transferred through
`List.toFinset_card_of_nodup`.  Nothing in the statements is
decidability-sensitive: `List.Nodup` mentions no instance, and the `Finset`
identities are proved by extensionality, so the classical instance baked
into `baseRelators` and `relators` is irrelevant to them. -/

section Counting

attribute [-instance] literalDecidableEq

/-- The six base letters `v₁,v₂,v₃,x,y,z` as a list. -/
def baseGeneratorList : List BaseGenerator := List.finRange 6

@[simp] theorem mem_baseGeneratorList (i : BaseGenerator) :
    i ∈ baseGeneratorList :=
  List.mem_finRange i

/-- The eight letters `v₁,v₂,v₃,x,y,z,t,c` as a list. -/
def generatorList : List Generator :=
  (List.finRange 6).map Sum.inl ++ (List.finRange 2).map Sum.inr

@[simp] theorem mem_generatorList (i : Generator) : i ∈ generatorList := by
  obtain (j | j) := i <;> simp [generatorList]

/-- The twenty displayed base relators, in the printed order. -/
def baseRelatorList : List (FreeGroup BaseGenerator) :=
  [baseRelXCube, baseRelYCube, baseRelZSq, baseRelXZCube,
   baseRelYZCube, baseRelXInvZXY, baseRelYInvZYX, baseRelXYSix,
   baseRelV12, baseRelV13, baseRelV23,
   baseRelXV1, baseRelXV2, baseRelXV3,
   baseRelYV1, baseRelYV2, baseRelYV3,
   baseRelZV1, baseRelZV2, baseRelZV3]

@[simp] theorem baseRelatorList_length : baseRelatorList.length = 20 := rfl

/-- The twenty displayed base relators are pairwise distinct elements of the
free group on the six base letters. -/
theorem baseRelatorList_nodup : baseRelatorList.Nodup :=
  List.Nodup.of_map FreeGroup.toWord (by decide)

theorem mem_baseRelators_iff_mem_list (r : FreeGroup BaseGenerator) :
    r ∈ baseRelators ↔ r ∈ baseRelatorList := by
  simp only [baseRelators, baseRelatorList, List.mem_toFinset]

theorem baseRelators_eq_toFinset :
    baseRelators = baseRelatorList.toFinset := by
  ext r
  rw [List.mem_toFinset]
  exact mem_baseRelators_iff_mem_list r

/-- **The literal base presentation has exactly twenty relators.** -/
theorem baseRelators_card : baseRelators.card = 20 := by
  rw [baseRelators_eq_toFinset,
    List.toFinset_card_of_nodup baseRelatorList_nodup, baseRelatorList_length]

/-- The twenty transported base relators, as words in the eight letters. -/
def transportedBaseRelatorList : List (FreeGroup Generator) :=
  baseRelatorList.map embedBaseWord

/-- The six stable-letter relators. -/
def stableRelatorList : List (FreeGroup Generator) :=
  baseGeneratorList.map stableRelator

/-- The seven lamp relators: the involution relation and six commutators. -/
def lampRelatorList : List (FreeGroup Generator) :=
  lampWord ^ 2 ::
    baseGeneratorList.map (fun i ↦ commutatorWord lampWord (vertexLetter i))

/-- The eight centrality relators for the marked word. -/
def markedRelatorList : List (FreeGroup Generator) :=
  generatorList.map (fun i ↦ commutatorWord markedWord (FreeGroup.of i))

/-- All forty-one displayed relators, in the printed order. -/
def relatorList : List (FreeGroup Generator) :=
  transportedBaseRelatorList ++ stableRelatorList ++ lampRelatorList ++
    markedRelatorList

@[simp] theorem relatorList_length : relatorList.length = 41 := rfl

/-- The forty-one displayed relators are pairwise distinct elements of the
free group on the eight letters. -/
theorem relatorList_nodup : relatorList.Nodup :=
  List.Nodup.of_map FreeGroup.toWord (by decide)

theorem mem_transportedBaseRelators_iff (r : FreeGroup Generator) :
    r ∈ transportedBaseRelators ↔ r ∈ transportedBaseRelatorList := by
  simp only [transportedBaseRelators, transportedBaseRelatorList,
    Finset.mem_image, List.mem_map, mem_baseRelators_iff_mem_list]

theorem mem_stableRelators_iff (r : FreeGroup Generator) :
    r ∈ stableRelators ↔ r ∈ stableRelatorList := by
  simp only [stableRelators, stableRelatorList, Finset.mem_image,
    Finset.mem_univ, true_and, List.mem_map, mem_baseGeneratorList]

theorem mem_lampRelators_iff (r : FreeGroup Generator) :
    r ∈ lampRelators ↔ r ∈ lampRelatorList := by
  simp only [lampRelators, lampRelatorList, Finset.mem_union,
    Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and,
    List.mem_cons, List.mem_map, mem_baseGeneratorList]

theorem mem_markedRelators_iff (r : FreeGroup Generator) :
    r ∈ markedRelators ↔ r ∈ markedRelatorList := by
  simp only [markedRelators, markedRelatorList, Finset.mem_image,
    Finset.mem_univ, true_and, List.mem_map, mem_generatorList]

theorem mem_relators_iff_mem_list (r : FreeGroup Generator) :
    r ∈ relators ↔ r ∈ relatorList := by
  simp only [relators, Finset.mem_union, mem_transportedBaseRelators_iff,
    mem_stableRelators_iff, mem_lampRelators_iff, mem_markedRelators_iff,
    relatorList, List.mem_append]

theorem relators_eq_toFinset : relators = relatorList.toFinset := by
  ext r
  rw [List.mem_toFinset]
  exact mem_relators_iff_mem_list r

/-- **The literal eight-generator presentation has exactly forty-one
relators.** -/
theorem relators_card : relators.card = 41 := by
  rw [relators_eq_toFinset,
    List.toFinset_card_of_nodup relatorList_nodup, relatorList_length]

end Counting

/-- The fixed literal object is an eight-generator finitely presented group.
This compact identity theorem is kept separate from the exact relator package
and from the mathematical conclusions of Theorem A. -/
theorem literalEightGeneratorPresentation :
    Fintype.card Generator = 8 ∧
      Group.IsFinitelyPresented MarkedGroup :=
  ⟨generator_card, inferInstance⟩

/-- Exact object-and-relator package for the manuscript's displayed
eight-generator presentation.  The first two conjuncts pin the alphabet and
the presented quotient itself; the remaining conjuncts record the relations
used immediately after the definition in the manuscript. -/
theorem manuscriptLiteralPresentation :
    Fintype.card Generator = 8 ∧
      (v1Index = 0 ∧ v2Index = 1 ∧ v3Index = 2 ∧
        xIndex = 3 ∧ yIndex = 4 ∧ zIndex = 5 ∧
        (Generator.stable : Generator) = Sum.inr 0 ∧
        (Generator.lamp : Generator) = Sum.inr 1) ∧
      baseRelators =
        [bx ^ 3, bY ^ 3, bz ^ 2, (bx * bz) ^ 3, (bY * bz) ^ 3,
          (bx⁻¹ * bz * bx * bY) ^ 2,
          (bY⁻¹ * bz * bY * bx) ^ 2, (bx * bY) ^ 6,
          bv1 * bv2 * bv1⁻¹ * bv2⁻¹,
          bv1 * bv3 * bv1⁻¹ * bv3⁻¹,
          bv2 * bv3 * bv2⁻¹ * bv3⁻¹,
          bx * bv1 * bx⁻¹ * bv3⁻¹,
          bx * bv2 * bx⁻¹ * bv1⁻¹,
          bx * bv3 * bx⁻¹ * bv2⁻¹,
          bY * bv1 * bY⁻¹ * bv1⁻¹,
          bY * bv2 * bY⁻¹ * (bv2⁻¹ * bv3)⁻¹,
          bY * bv3 * bY⁻¹ * (bv1 * bv2⁻¹)⁻¹,
          bz * bv1 * bz⁻¹ * (bv2 * bv3⁻¹)⁻¹,
          bz * bv2 * bz⁻¹ * (bv1 * bv3⁻¹)⁻¹,
          bz * bv3 * bz⁻¹ * (bv3⁻¹)⁻¹].toFinset ∧
      baseRelators.card = 20 ∧
      transportedBaseRelators = baseRelators.image embedBaseWord ∧
      (compressedBaseWord v1Index = bv1 ^ 2 ∧
        compressedBaseWord v2Index = bv2 ^ 2 ∧
        compressedBaseWord v3Index = bv3 ^ 2 ∧
        compressedBaseWord xIndex = bx ∧
        compressedBaseWord yIndex = bY ∧
        compressedBaseWord zIndex = bz) ∧
      stableRelators = Finset.univ.image (fun i : BaseGenerator ↦
        stableWord * vertexLetter i * stableWord⁻¹ *
          (embedBaseWord (compressedBaseWord i))⁻¹) ∧
      lampRelators =
        {lampWord ^ 2} ∪ Finset.univ.image (fun i : BaseGenerator ↦
          lampWord * vertexLetter i * lampWord⁻¹ * (vertexLetter i)⁻¹) ∧
      markedWord =
        (let displaced := stableWord * lampWord * stableWord⁻¹
         displaced * (v1Word * displaced * v1Word⁻¹) * displaced⁻¹ *
           (v1Word * displaced * v1Word⁻¹)⁻¹) ∧
      markedRelators =
        Finset.univ.image (fun i : Generator ↦
          markedWord * FreeGroup.of i * markedWord⁻¹ *
            (FreeGroup.of i)⁻¹) ∧
      relators =
        transportedBaseRelators ∪ stableRelators ∪ lampRelators ∪
          markedRelators ∧
      relators.card = 41 ∧
      MarkedGroup =
        PresentedGroup ((relators : Finset (FreeGroup Generator)) :
          Set (FreeGroup Generator)) ∧
      Group.IsFinitelyPresented MarkedGroup ∧
      (mark ^ 2 = 1 ∧ ∀ g : MarkedGroup, Commute mark g) ∧
      (∀ g : Base, stable * baseMap g * stable⁻¹ ∈ baseMap.range) ∧
      (∀ g : Base, Commute lamp (baseMap g)) := by
  exact ⟨generator_card,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, baseRelators_card, rfl,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, relators_card, rfl,
    inferInstance,
    ⟨mark_sq, mark_central⟩, stable_conjugates_base_into_base,
    lamp_commutes_base⟩

end

end LiteralNonMFPresentation
end GroupApproximation
