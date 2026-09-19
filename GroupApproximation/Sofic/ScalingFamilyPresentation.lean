import GroupApproximation.Sofic.LiteralNonMFPresentation

/-!
# The scaling family of eight-generator presentations

`LiteralNonMFPresentation` fixes the six stable-letter relations in the form
`t vᵢ t⁻¹ = vᵢ²`.  Nothing else in that presentation refers to the exponent:
the twenty base relators, the lamp relators and the marked relators are all
independent of it, and so is the property `(T)` of the base.  This file
therefore reruns the construction with a parameter `m`, producing for every
natural number a presented group `MarkedGroup m` on the same eight
generators.

Only the stable relators move, so `transportedBaseRelators`, `lampRelators`,
`markedRelators`, `markedWord` and the base group `Base` itself are imported
unchanged.  `relators_two` records that `m = 2` returns the literal group of
the manuscript on the nose, and every later declaration of this file
specializes at `m = 2` to its counterpart in `LiteralNonMFPresentation`.

Note that the involution exponents `lamp ^ 2 = 1` and `mark ^ 2 = 1` are
Clifford data, not scaling data: they stay at `2` for every `m`.
-/

namespace GroupApproximation
namespace ScalingFamilyPresentation

open LiteralNonMFPresentation

open scoped commutatorElement

noncomputable section

local instance scalingDecidableEq {α : Type*} : DecidableEq α :=
  Classical.decEq α

/-! ## The scaled stable relators -/

/-- The right-hand side of the stable-letter relation for scaling factor
`m`, before embedding it in the final alphabet. -/
def compressedBaseWord (m : ℕ) (i : BaseGenerator) : FreeGroup BaseGenerator :=
  if i = v1Index then bv1 ^ m
  else if i = v2Index then bv2 ^ m
  else if i = v3Index then bv3 ^ m
  else if i = xIndex then bx
  else if i = yIndex then bY
  else bz

/-- Scaling factor `2` is the literal manuscript presentation. -/
@[simp] theorem compressedBaseWord_two :
    compressedBaseWord 2 = LiteralNonMFPresentation.compressedBaseWord := rfl

/-- The right-hand side of the stable-letter relation for a base generator. -/
def compressedGeneratorWord (m : ℕ) (i : BaseGenerator) : FreeGroup Generator :=
  embedBaseWord (compressedBaseWord m i)

/-- `t s t⁻¹ = compressedGeneratorWord m s`. -/
def stableRelator (m : ℕ) (i : BaseGenerator) : FreeGroup Generator :=
  stableWord * vertexLetter i * stableWord⁻¹ * (compressedGeneratorWord m i)⁻¹

noncomputable def stableRelators (m : ℕ) : Finset (FreeGroup Generator) :=
  Finset.univ.image (stableRelator m)

/-- All relators in the `m`-th eight-generator presentation. -/
noncomputable def relators (m : ℕ) : Finset (FreeGroup Generator) :=
  transportedBaseRelators ∪ stableRelators m ∪ lampRelators ∪ markedRelators

/-- The `m`-th group of the family. -/
noncomputable abbrev MarkedGroup (m : ℕ) : Type :=
  PresentedGroup ((relators m : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

/-- The family's second member is the literal manuscript group `E`. -/
@[simp] theorem relators_two : relators 2 = LiteralNonMFPresentation.relators := rfl

instance markedGroup_finitelyPresented (m : ℕ) :
    Group.IsFinitelyPresented (MarkedGroup m) := inferInstance

noncomputable instance markedGroup_countable (m : ℕ) :
    Countable (MarkedGroup m) :=
  (PresentedGroup.mk_surjective
    ((relators m : Finset (FreeGroup Generator)) :
      Set (FreeGroup Generator))).countable

noncomputable abbrev wordInMarkedGroup (m : ℕ) :
    FreeGroup Generator →* MarkedGroup m :=
  PresentedGroup.mk ((relators m : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

noncomputable abbrev stable (m : ℕ) : MarkedGroup m :=
  wordInMarkedGroup m stableWord
noncomputable abbrev lamp (m : ℕ) : MarkedGroup m :=
  wordInMarkedGroup m lampWord
noncomputable abbrev mark (m : ℕ) : MarkedGroup m :=
  wordInMarkedGroup m markedWord

/-! ## The canonical base homomorphism -/

/-- The canonical map from the literal six-generator base into `E_m`. -/
noncomputable def baseMap (m : ℕ) : Base →* MarkedGroup m := by
  apply PresentedGroup.toGroup
    (f := fun i : BaseGenerator ↦ wordInMarkedGroup m (vertexLetter i))
  intro r hr
  rw [← lift_embedBaseWord
    (f := fun j : Generator ↦ wordInMarkedGroup m (FreeGroup.of j))]
  rw [freeGroup_lift_presentedGroup_generators]
  apply PresentedGroup.one_of_mem
  change embedBaseWord r ∈ relators m
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl
    (Finset.mem_image.mpr ⟨r, Finset.mem_coe.mp hr, rfl⟩)))

@[simp] theorem baseMap_generator (m : ℕ) (i : BaseGenerator) :
    baseMap m (PresentedGroup.of i) = wordInMarkedGroup m (vertexLetter i) :=
  PresentedGroup.toGroup.of _

theorem baseMap_mk (m : ℕ) (w : FreeGroup BaseGenerator) :
    baseMap m (PresentedGroup.mk _ w) =
      wordInMarkedGroup m (embedBaseWord w) := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ w) = _
  rw [presentedToGroup_mk]
  rw [← lift_embedBaseWord
    (f := fun j : Generator ↦ wordInMarkedGroup m (FreeGroup.of j))]
  rw [freeGroup_lift_presentedGroup_generators]

/-- Each displayed stable relation holds in the presented group. -/
theorem stable_relation (m : ℕ) (i : BaseGenerator) :
    stable m * baseMap m (PresentedGroup.of i) * (stable m)⁻¹ =
      wordInMarkedGroup m (compressedGeneratorWord m i) := by
  have hrel : wordInMarkedGroup m (stableRelator m i) = 1 := by
    apply PresentedGroup.one_of_mem
    change stableRelator m i ∈ relators m
    simp only [relators, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))
  simp only [stableRelator, map_mul, map_inv] at hrel
  exact mul_inv_eq_one.mp hrel

/-- Conjugation by `t` sends the entire image of the literal base back into
that image. -/
theorem stable_conjugates_base_into_base (m : ℕ) :
    ∀ g : Base, stable m * baseMap m g * (stable m)⁻¹ ∈ (baseMap m).range := by
  intro g
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      rw [show PresentedGroup.mk _ (FreeGroup.of i) =
        PresentedGroup.of i from rfl]
      rw [stable_relation]
      exact ⟨PresentedGroup.mk _ (compressedBaseWord m i), baseMap_mk m _⟩
  | inv_of i hi =>
      have hinv := (baseMap m).range.inv_mem hi
      rw [map_inv]
      have heq :
          stable m * (baseMap m (PresentedGroup.mk _ (FreeGroup.of i)))⁻¹ *
              (stable m)⁻¹ =
            (stable m * baseMap m (PresentedGroup.mk _ (FreeGroup.of i)) *
              (stable m)⁻¹)⁻¹ := by group
      exact (congrArg (fun q : MarkedGroup m ↦ q ∈ (baseMap m).range) heq).mpr
        hinv
  | mul a b ha hb =>
      rw [map_mul]
      rw [map_mul (baseMap m)]
      have hmul := (baseMap m).range.mul_mem ha hb
      have heq :
          stable m *
              (baseMap m (PresentedGroup.mk _ a) *
                baseMap m (PresentedGroup.mk _ b)) * (stable m)⁻¹ =
            (stable m * baseMap m (PresentedGroup.mk _ a) * (stable m)⁻¹) *
              (stable m * baseMap m (PresentedGroup.mk _ b) * (stable m)⁻¹) := by
        group
      exact (congrArg (fun q : MarkedGroup m ↦ q ∈ (baseMap m).range) heq).mpr
        hmul

/-! ## Centrality relations -/

theorem lamp_commutes_base_generator (m : ℕ) (i : BaseGenerator) :
    Commute (lamp m) (baseMap m (PresentedGroup.of i)) := by
  rw [baseMap_generator]
  have hcomm : wordInMarkedGroup m
      (commutatorWord lampWord (vertexLetter i)) = 1 := by
    apply PresentedGroup.one_of_mem
    change commutatorWord lampWord (vertexLetter i) ∈ relators m
    simp [relators, lampRelators]
  rw [map_commutatorWord] at hcomm
  exact commutatorElement_eq_one_iff_commute.mp hcomm

theorem lamp_commutes_base (m : ℕ) (g : Base) :
    Commute (lamp m) (baseMap m g) := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ g
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_right _
  | of i =>
      rw [show PresentedGroup.mk _ (FreeGroup.of i) =
        PresentedGroup.of i from rfl]
      exact lamp_commutes_base_generator m i
  | inv_of i hi =>
      rw [map_inv]
      exact hi.inv_right
  | mul a b ha hb =>
      simpa only [map_mul] using ha.mul_right hb

theorem lamp_sq (m : ℕ) : lamp m ^ 2 = 1 := by
  apply PresentedGroup.one_of_mem
  change lampWord ^ 2 ∈ relators m
  simp [relators, lampRelators]

theorem mark_central (m : ℕ) (g : MarkedGroup m) : Commute (mark m) g := by
  have hgen : ∀ i : Generator,
      Commute (mark m) (wordInMarkedGroup m (FreeGroup.of i)) := by
    intro i
    have hcomm : wordInMarkedGroup m
        (commutatorWord markedWord (FreeGroup.of i)) = 1 := by
      apply PresentedGroup.one_of_mem
      change commutatorWord markedWord (FreeGroup.of i) ∈ relators m
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

/-- The marked element is the analytic marked-compression word. -/
theorem mark_eq_markedCompressionWord (m : ℕ) :
    mark m = markedCompressionWord (stable m)
      (baseMap m (PresentedGroup.of v1Index)) (lamp m) := by
  simp only [mark, markedWord, markedCompressionWord, commutatorWord,
    displacedLampWord, v1Word, stable, lamp, map_mul, map_inv,
    baseMap_generator]
  group

theorem mark_sq (m : ℕ) : mark m ^ 2 = 1 := by
  rw [mark_eq_markedCompressionWord]
  exact markedCompressionWord_sq_eq_one_of_c_sq_of_central
    (stable m) (baseMap m (PresentedGroup.of v1Index)) (lamp m) (lamp_sq m)
    (fun g ↦ by
      rw [← mark_eq_markedCompressionWord]
      exact mark_central m g)

/-! ## Exact-realization interface -/

/-- Data sufficient to evaluate every relator of the `m`-th presentation in
an arbitrary group. -/
structure Realization (m : ℕ) (M : Type*) [Group M] where
  baseGenerator : BaseGenerator → M
  stable : M
  lamp : M
  base_relations : ∀ r ∈ baseRelators,
    FreeGroup.lift baseGenerator r = 1
  stable_relations : ∀ i : BaseGenerator,
    stable * baseGenerator i * stable⁻¹ =
      FreeGroup.lift baseGenerator (compressedBaseWord m i)
  lamp_sq : lamp ^ 2 = 1
  lamp_centralizes_base : ∀ i, Commute lamp (baseGenerator i)
  marked_central : ∀ g : M,
    Commute (markedCompressionWord stable (baseGenerator v1Index) lamp) g

variable {m : ℕ} {M : Type*} [Group M]

def realizationGenerator (R : Realization m M) : Generator → M
  | .inl i => R.baseGenerator i
  | .inr j => if j = 0 then R.stable else R.lamp

@[simp] theorem realizationGenerator_base (R : Realization m M)
    (i : BaseGenerator) :
    realizationGenerator R (Generator.base i) = R.baseGenerator i := rfl

@[simp] theorem realizationGenerator_stable (R : Realization m M) :
    realizationGenerator R Generator.stable = R.stable := by
  simp [realizationGenerator]

@[simp] theorem realizationGenerator_lamp (R : Realization m M) :
    realizationGenerator R Generator.lamp = R.lamp := by
  simp [realizationGenerator]

theorem realization_eval_base (R : Realization m M)
    (w : FreeGroup BaseGenerator) :
    FreeGroup.lift (realizationGenerator R) (embedBaseWord w) =
      FreeGroup.lift R.baseGenerator w := by
  rw [lift_embedBaseWord]
  rfl

@[simp] theorem realization_eval_compressed (R : Realization m M)
    (i : BaseGenerator) :
    FreeGroup.lift (realizationGenerator R) (compressedGeneratorWord m i) =
      FreeGroup.lift R.baseGenerator (compressedBaseWord m i) :=
  realization_eval_base R (compressedBaseWord m i)

@[simp] theorem realization_eval_marked (R : Realization m M) :
    FreeGroup.lift (realizationGenerator R) markedWord =
      markedCompressionWord R.stable (R.baseGenerator v1Index) R.lamp := by
  simp [markedWord, markedCompressionWord, commutatorWord,
    displacedLampWord]
  group

/-- The universal homomorphism from the `m`-th presentation to a
realization. -/
noncomputable def realizationHom (R : Realization m M) : MarkedGroup m →* M := by
  apply PresentedGroup.toGroup (f := realizationGenerator R)
  intro r hr
  change r ∈ relators m at hr
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
  · have hr' : r ∈ ({lampWord ^ 2} : Finset (FreeGroup Generator)) ∪
        Finset.univ.image (fun i : BaseGenerator ↦
          commutatorWord lampWord (vertexLetter i)) := hr
    rcases Finset.mem_union.mp hr' with h1 | h2
    · rw [Finset.mem_singleton.mp h1]
      simpa using R.lamp_sq
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h2
      rw [map_commutatorWord,
        show FreeGroup.lift (realizationGenerator R) lampWord =
          R.lamp by simp [lampWord],
        show FreeGroup.lift (realizationGenerator R) (vertexLetter i) =
          R.baseGenerator i by simp [vertexLetter]]
      exact commutatorElement_eq_one_iff_commute.mpr
        (R.lamp_centralizes_base i)
  · unfold markedRelators at hr
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    rw [map_commutatorWord, realization_eval_marked,
      FreeGroup.lift_apply_of]
    exact commutatorElement_eq_one_iff_commute.mpr
      (R.marked_central (realizationGenerator R i))

@[simp] theorem realizationHom_base_generator (R : Realization m M)
    (i : BaseGenerator) :
    realizationHom R (baseMap m (PresentedGroup.of i)) = R.baseGenerator i := by
  rw [baseMap_generator]
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ (vertexLetter i)) = _
  rw [presentedToGroup_mk]
  simp [vertexLetter]

@[simp] theorem realizationHom_stable (R : Realization m M) :
    realizationHom R (stable m) = R.stable := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ stableWord) = _
  rw [presentedToGroup_mk]
  simp [stableWord]

@[simp] theorem realizationHom_lamp (R : Realization m M) :
    realizationHom R (lamp m) = R.lamp := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ lampWord) = _
  rw [presentedToGroup_mk]
  simp [lampWord]

@[simp] theorem realizationHom_mark (R : Realization m M) :
    realizationHom R (mark m) =
      markedCompressionWord R.stable (R.baseGenerator v1Index) R.lamp := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ markedWord) = _
  rw [presentedToGroup_mk, realization_eval_marked]

theorem mark_ne_one_of_realization (R : Realization m M)
    (hR : markedCompressionWord R.stable (R.baseGenerator v1Index) R.lamp ≠ 1) :
    mark m ≠ 1 := by
  intro h
  apply hR
  rw [← realizationHom_mark R, h, map_one]

end

end ScalingFamilyPresentation
end GroupApproximation
