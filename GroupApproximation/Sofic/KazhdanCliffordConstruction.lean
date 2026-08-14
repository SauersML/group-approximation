import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Kazhdan.KazhdanUniverse
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# The Kazhdan--Clifford construction

This file formalizes the conceptual non-MF construction independently of the
literal eight-generator presentation.  Starting with a finitely presented
property-`(T)` group `Γ`, an injective endomorphism `alpha`, and an element
`a` outside its range, it adjoins a stable letter `t` and a root involution
`c`.  The word

`w = [t c t⁻¹, a (t c t⁻¹) a⁻¹]`

is required only to be central.  Its square relation is *derived*, not
imposed.  A homomorphism to the mapping-telescope Clifford model sends `w`
to the nontrivial Clifford sign.  The short negative-central-corner
Kazhdan transport contradiction proves directly that the constructed
finitely presented group is not MF.  The stronger finite-normal theorem is
retained separately for the universal corona-kernel conclusion.
-/

namespace GroupApproximation
namespace KazhdanCliffordConstruction

open scoped commutatorElement

noncomputable section

universe w

variable {Γ : Type} [Group Γ] [Group.IsFinitelyPresented Γ]

/-! ## A chosen finite generating map for the base -/

/-- Finite generating data extracted from finite presentability.  Only the
surjective evaluation map is needed because the base group itself is one
factor of the relative presentation. -/
structure GeneratorData (Γ : Type) [Group Γ] where
  count : ℕ
  eval : FreeGroup (Fin count) →* Γ
  surjective : Function.Surjective eval

/-- A fixed finite generating map for a finitely presented group. -/
noncomputable def generatorData : GeneratorData Γ := by
  obtain ⟨n, eval, heval, -⟩ := Group.IsFinitelyPresented.out (G := Γ)
  exact ⟨n, eval, heval⟩

abbrev generatorCount : ℕ := (generatorData (Γ := Γ)).count

noncomputable abbrev baseEval : FreeGroup (Fin generatorCount) →* Γ :=
  (generatorData (Γ := Γ)).eval

theorem baseEval_surjective : Function.Surjective (baseEval (Γ := Γ)) :=
  (generatorData (Γ := Γ)).surjective

/-! ## The relative finite presentation -/

/-- The free product of the base with the free group on `t,c`. -/
abbrev Raw (Γ : Type) [Group Γ] := Monoid.Coprod Γ (FreeGroup (Fin 2))

noncomputable abbrev rawBase (g : Γ) : Raw Γ := Monoid.Coprod.inl g
noncomputable abbrev rawStable : Raw Γ := Monoid.Coprod.inr (FreeGroup.of 0)
noncomputable abbrev rawLamp : Raw Γ := Monoid.Coprod.inr (FreeGroup.of 1)

noncomputable def rawMark (a : Γ) : Raw Γ :=
  markedCompressionWord rawStable (rawBase a) rawLamp

noncomputable def stableRelator (alpha : Γ →* Γ)
    (i : Fin generatorCount) : Raw Γ :=
  rawStable * rawBase (baseEval (FreeGroup.of i)) * rawStable⁻¹ *
    (rawBase (alpha (baseEval (FreeGroup.of i))))⁻¹

noncomputable def stableRelators (alpha : Γ →* Γ) : Finset (Raw Γ) :=
  Finset.univ.image (stableRelator alpha)

noncomputable def lampRelators : Finset (Raw Γ) :=
  {rawLamp ^ 2} ∪ Finset.univ.image (fun i : Fin generatorCount ↦
    ⁅rawLamp, rawBase (baseEval (FreeGroup.of i))⁆)

/-- Centrality relators for the marked word.  There is deliberately no
`rawMark a ^ 2` relator. -/
noncomputable def centralRelators (a : Γ) : Finset (Raw Γ) :=
  {⁅rawMark a, rawStable⁆, ⁅rawMark a, rawLamp⁆} ∪
    Finset.univ.image (fun i : Fin generatorCount ↦
      ⁅rawMark a, rawBase (baseEval (FreeGroup.of i))⁆)

noncomputable def relators (alpha : Γ →* Γ) (a : Γ) : Finset (Raw Γ) :=
  stableRelators alpha ∪ lampRelators ∪ centralRelators a

noncomputable def relations (alpha : Γ →* Γ) (a : Γ) : Subgroup (Raw Γ) :=
  Subgroup.normalClosure (relators alpha a : Set (Raw Γ))

instance relations_normal (alpha : Γ →* Γ) (a : Γ) :
    (relations alpha a).Normal := Subgroup.normalClosure_normal

/-- The finitely presented Kazhdan--Clifford extension. -/
noncomputable abbrev Extension (alpha : Γ →* Γ) (a : Γ) : Type :=
  Raw Γ ⧸ relations alpha a

instance extension_group (alpha : Γ →* Γ) (a : Γ) :
    Group (Extension alpha a) := inferInstance

theorem relations_finitelyNormallyGenerated (alpha : Γ →* Γ) (a : Γ) :
    (relations alpha a).IsFinitelyNormallyGenerated :=
  ⟨(relators alpha a : Set (Raw Γ)), Set.toFinite _, rfl⟩

instance extension_finitelyPresented (alpha : Γ →* Γ) (a : Γ) :
    Group.IsFinitelyPresented (Extension alpha a) :=
  Group.IsFinitelyPresented.quotient (relations alpha a)
    (relations_finitelyNormallyGenerated alpha a)

noncomputable abbrev quotientMap (alpha : Γ →* Γ) (a : Γ) :
    Raw Γ →* Extension alpha a := QuotientGroup.mk' (relations alpha a)

noncomputable def iota (alpha : Γ →* Γ) (a : Γ) : Γ →* Extension alpha a :=
  (quotientMap alpha a).comp Monoid.Coprod.inl

noncomputable def stable (alpha : Γ →* Γ) (a : Γ) : Extension alpha a :=
  quotientMap alpha a rawStable

noncomputable def lamp (alpha : Γ →* Γ) (a : Γ) : Extension alpha a :=
  quotientMap alpha a rawLamp

noncomputable def displaced (alpha : Γ →* Γ) (a : Γ) : Extension alpha a :=
  stable alpha a * lamp alpha a * (stable alpha a)⁻¹

noncomputable def mark (alpha : Γ →* Γ) (a : Γ) : Extension alpha a :=
  markedCompressionWord (stable alpha a) (iota alpha a a) (lamp alpha a)

theorem quotientMap_relator_eq_one {alpha : Γ →* Γ} {a : Γ}
    {r : Raw Γ} (hr : r ∈ relators alpha a) :
    quotientMap alpha a r = 1 :=
  (QuotientGroup.eq_one_iff r).mpr
    (Subgroup.subset_normalClosure hr)

@[simp] theorem quotientMap_rawBase (alpha : Γ →* Γ) (a g : Γ) :
    quotientMap alpha a (rawBase g) = iota alpha a g := rfl

@[simp] theorem quotientMap_rawStable (alpha : Γ →* Γ) (a : Γ) :
    quotientMap alpha a rawStable = stable alpha a := rfl

@[simp] theorem quotientMap_rawLamp (alpha : Γ →* Γ) (a : Γ) :
    quotientMap alpha a rawLamp = lamp alpha a := rfl

@[simp] theorem quotientMap_rawMark (alpha : Γ →* Γ) (a : Γ) :
    quotientMap alpha a (rawMark a) = mark alpha a := by
  simp [rawMark, mark, map_markedCompressionWord]

/-! ## Exact consequences of the finite relators -/

theorem stable_compresses_generator (alpha : Γ →* Γ) (a : Γ)
    (i : Fin generatorCount) :
    stable alpha a * iota alpha a (baseEval (FreeGroup.of i)) *
        (stable alpha a)⁻¹ =
      iota alpha a (alpha (baseEval (FreeGroup.of i))) := by
  have h := quotientMap_relator_eq_one
    (alpha := alpha) (a := a)
    (show stableRelator alpha i ∈ relators alpha a by
      simp [relators, stableRelators])
  simpa [stableRelator] using mul_inv_eq_one.mp h

/-- The finitely many stable-letter relators imply the compression relation
for every element of the base. -/
theorem stable_compresses (alpha : Γ →* Γ) (a g : Γ) :
    stable alpha a * iota alpha a g * (stable alpha a)⁻¹ =
      iota alpha a (alpha g) := by
  obtain ⟨w, rfl⟩ := baseEval_surjective (Γ := Γ) g
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i => exact stable_compresses_generator alpha a i
  | inv_of i hi =>
      rw [map_inv, map_inv, map_inv]
      calc
        stable alpha a * (iota alpha a (baseEval (FreeGroup.of i)))⁻¹ *
              (stable alpha a)⁻¹ =
            (stable alpha a * iota alpha a (baseEval (FreeGroup.of i)) *
              (stable alpha a)⁻¹)⁻¹ := by group
        _ = (iota alpha a (alpha (baseEval (FreeGroup.of i))))⁻¹ := by rw [hi]
  | mul x y hx hy =>
      rw [map_mul, map_mul, map_mul]
      calc
        stable alpha a *
              (iota alpha a (baseEval x) * iota alpha a (baseEval y)) *
              (stable alpha a)⁻¹ =
            (stable alpha a * iota alpha a (baseEval x) *
              (stable alpha a)⁻¹) *
            (stable alpha a * iota alpha a (baseEval y) *
              (stable alpha a)⁻¹) := by group
        _ = iota alpha a (alpha (baseEval x)) *
              iota alpha a (alpha (baseEval y)) := by rw [hx, hy]

theorem lamp_sq (alpha : Γ →* Γ) (a : Γ) : lamp alpha a ^ 2 = 1 := by
  simpa using quotientMap_relator_eq_one
    (alpha := alpha) (a := a)
    (show rawLamp ^ 2 ∈ relators alpha a by
      simp [relators, lampRelators])

theorem lamp_commutes_generator (alpha : Γ →* Γ) (a : Γ)
    (i : Fin generatorCount) :
    Commute (lamp alpha a) (iota alpha a (baseEval (FreeGroup.of i))) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [map_commutatorElement] using quotientMap_relator_eq_one
    (alpha := alpha) (a := a)
    (show ⁅rawLamp, rawBase (baseEval (FreeGroup.of i))⁆ ∈
        relators alpha a by simp [relators, lampRelators])

/-- The lamp centralizes the whole base. -/
theorem lamp_commutes (alpha : Γ →* Γ) (a g : Γ) :
    Commute (lamp alpha a) (iota alpha a g) := by
  obtain ⟨w, rfl⟩ := baseEval_surjective (Γ := Γ) g
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i => exact lamp_commutes_generator alpha a i
  | inv_of i hi => simpa using hi.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

theorem mark_commutes_stable (alpha : Γ →* Γ) (a : Γ) :
    Commute (mark alpha a) (stable alpha a) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [map_commutatorElement] using quotientMap_relator_eq_one
    (alpha := alpha) (a := a)
    (show ⁅rawMark a, rawStable⁆ ∈ relators alpha a by
      simp [relators, centralRelators])

theorem mark_commutes_lamp (alpha : Γ →* Γ) (a : Γ) :
    Commute (mark alpha a) (lamp alpha a) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [map_commutatorElement] using quotientMap_relator_eq_one
    (alpha := alpha) (a := a)
    (show ⁅rawMark a, rawLamp⁆ ∈ relators alpha a by
      simp [relators, centralRelators])

theorem mark_commutes_base_generator (alpha : Γ →* Γ) (a : Γ)
    (i : Fin generatorCount) :
    Commute (mark alpha a) (iota alpha a (baseEval (FreeGroup.of i))) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa [map_commutatorElement] using quotientMap_relator_eq_one
    (alpha := alpha) (a := a)
    (show ⁅rawMark a, rawBase (baseEval (FreeGroup.of i))⁆ ∈
        relators alpha a by simp [relators, centralRelators])

theorem mark_commutes_base (alpha : Γ →* Γ) (a g : Γ) :
    Commute (mark alpha a) (iota alpha a g) := by
  obtain ⟨w, rfl⟩ := baseEval_surjective (Γ := Γ) g
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i => exact mark_commutes_base_generator alpha a i
  | inv_of i hi => simpa using hi.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

theorem mark_commutes_free (alpha : Γ →* Γ) (a : Γ)
    (w : FreeGroup (Fin 2)) :
    Commute (mark alpha a) (quotientMap alpha a (Monoid.Coprod.inr w)) := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · exact mark_commutes_stable alpha a
      · exact mark_commutes_lamp alpha a
  | inv_of i hi => simpa using hi.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

/-- The marked word is central in the whole presented group. -/
theorem mark_central (alpha : Γ →* Γ) (a : Γ)
    (x : Extension alpha a) : Commute (mark alpha a) x := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (relations alpha a) x
  induction r using Monoid.Coprod.induction_on with
  | inl g => exact mark_commutes_base alpha a g
  | inr w => exact mark_commutes_free alpha a w
  | mul x y hx hy => simpa using hx.mul_right hy

/-- Conjugating the root involution shows that the displaced lamp is an
involution. -/
theorem displaced_sq (alpha : Γ →* Γ) (a : Γ) :
    displaced alpha a ^ 2 = 1 := by
  simp only [displaced, pow_two]
  have hc := lamp_sq alpha a
  rw [pow_two] at hc
  calc
    (stable alpha a * lamp alpha a * (stable alpha a)⁻¹) *
          (stable alpha a * lamp alpha a * (stable alpha a)⁻¹) =
        stable alpha a * (lamp alpha a * lamp alpha a) *
          (stable alpha a)⁻¹ := by group
    _ = 1 := by rw [hc]; group

/-- **The involution relation is redundant.**  Centrality of the marked word
and involutivity of the displaced lamp force `w²=1`. -/
theorem mark_sq (alpha : Γ →* Γ) (a : Γ) : mark alpha a ^ 2 = 1 := by
  exact markedCompressionWord_sq_eq_one_of_c_sq_of_central
    (stable alpha a) (iota alpha a a) (lamp alpha a)
    (lamp_sq alpha a) (mark_central alpha a)

/-! ## The HNN--Clifford witness -/

variable (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha) (a : Γ)

noncomputable def freeRealization : FreeGroup (Fin 2) →*
    MarkedCompression.Ambient alpha hAlpha :=
  FreeGroup.lift (fun i ↦ if i = 0 then
    MarkedCompression.tAmbient alpha hAlpha
  else MarkedCompression.cAmbient alpha hAlpha)

noncomputable def rawRealization : Raw Γ →*
    MarkedCompression.Ambient alpha hAlpha :=
  Monoid.Coprod.lift (MarkedCompression.iotaAmbient alpha hAlpha)
    (freeRealization alpha hAlpha)

@[simp] theorem rawRealization_base (g : Γ) :
    rawRealization alpha hAlpha (rawBase g) =
      MarkedCompression.iotaAmbient alpha hAlpha g := rfl

@[simp] theorem rawRealization_stable :
    rawRealization alpha hAlpha rawStable =
      MarkedCompression.tAmbient alpha hAlpha := by
  simp [rawRealization, freeRealization, rawStable]

@[simp] theorem rawRealization_lamp :
    rawRealization alpha hAlpha rawLamp =
      MarkedCompression.cAmbient alpha hAlpha := by
  simp [rawRealization, freeRealization, rawLamp]

theorem rawRealization_mark (ha : a ∉ Set.range alpha) :
    rawRealization alpha hAlpha (rawMark a) =
      MarkedCompression.signAmbient alpha hAlpha := by
  rw [rawMark, map_markedCompressionWord]
  simp only [rawRealization_stable, rawRealization_base, rawRealization_lamp]
  exact MarkedCompression.marked_word_eq_sign alpha hAlpha ha

theorem relators_le_rawRealization_ker (ha : a ∉ Set.range alpha) :
    relations alpha a ≤ (rawRealization alpha hAlpha).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  change r ∈ relators alpha a at hr
  simp only [relators, Finset.mem_union] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    apply MonoidHom.mem_ker.mpr
    simp only [stableRelator, map_mul, map_inv, rawRealization_stable,
      rawRealization_base]
    exact mul_inv_eq_one.mpr (MarkedCompression.compress alpha hAlpha _)
  · simp only [lampRelators, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image] at hr
    rcases hr with rfl | ⟨i, -, rfl⟩
    · apply MonoidHom.mem_ker.mpr
      simpa using MarkedCompression.cAmbient_sq alpha hAlpha
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr
        (MarkedCompression.comm_c alpha hAlpha _)
  · simp only [centralRelators, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_image] at hr
    rcases hr with (rfl | rfl) | ⟨i, -, rfl⟩
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawRealization_mark ha]
      exact commutatorElement_eq_one_iff_commute.mpr
        (MarkedCompression.signAmbient_central alpha hAlpha _)
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawRealization_mark ha]
      exact commutatorElement_eq_one_iff_commute.mpr
        (MarkedCompression.signAmbient_central alpha hAlpha _)
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawRealization_mark ha]
      exact commutatorElement_eq_one_iff_commute.mpr
        (MarkedCompression.signAmbient_central alpha hAlpha _)

noncomputable def cliffordHom (ha : a ∉ Set.range alpha) :
    Extension alpha a →* MarkedCompression.Ambient alpha hAlpha :=
  QuotientGroup.lift (relations alpha a) (rawRealization alpha hAlpha)
    (relators_le_rawRealization_ker alpha hAlpha a ha)

@[simp] theorem cliffordHom_quotientMap (ha : a ∉ Set.range alpha)
    (r : Raw Γ) :
    cliffordHom alpha hAlpha a ha (quotientMap alpha a r) =
      rawRealization alpha hAlpha r :=
  QuotientGroup.lift_mk' _ _ r

theorem cliffordHom_mark (ha : a ∉ Set.range alpha) :
    cliffordHom alpha hAlpha a ha (mark alpha a) =
      MarkedCompression.signAmbient alpha hAlpha := by
  rw [← quotientMap_rawMark, cliffordHom_quotientMap,
    rawRealization_mark alpha hAlpha a ha]

/-- The marked word survives because its Clifford realization is the
nontrivial central sign. -/
theorem mark_ne_one (ha : a ∉ Set.range alpha) : mark alpha a ≠ 1 := by
  intro h
  apply MarkedCompression.signAmbient_ne_one alpha hAlpha
  rw [← cliffordHom_mark alpha hAlpha a ha, h, map_one]

/-- The base embeds in the constructed extension; the Clifford map is a left
inverse after composing with the already faithful telescope embedding. -/
theorem iota_injective (ha : a ∉ Set.range alpha) :
    Function.Injective (iota alpha a) := by
  intro x y hxy
  apply MarkedCompression.iotaAmbient_injective alpha hAlpha
  have := congrArg (cliffordHom alpha hAlpha a ha) hxy
  simpa [iota, rawRealization] using this

/-! ## Kazhdan cancellation and the non-MF endpoint -/

variable (hT : HasKazhdanPropertyT.{0, 0} Γ)

noncomputable def compressionCore :
    KazhdanCompressionCore Γ (Extension alpha a) where
  iota := iota alpha a
  t := stable alpha a
  c := lamp alpha a
  kazhdan := hT
  compresses g := ⟨alpha g, stable_compresses alpha a g⟩
  comm_c := lamp_commutes alpha a

/-- The conceptual construction as marked inclusion data.  The central-sign
order-two relation is filled by the derived theorem `mark_sq`; it is not a
presentation relator. -/
noncomputable def inclusionData :
    MarkedCompressionInclusionData Γ (Extension alpha a) where
  iota := iota alpha a
  t := stable alpha a
  c := lamp alpha a
  a := a
  kazhdan := hT
  compresses g := ⟨alpha g, stable_compresses alpha a g⟩
  comm_c := lamp_commutes alpha a
  word_sq := by simpa [MarkedCompressionInclusionData.word, mark] using
    mark_sq alpha a
  word_central g := by
    simpa [MarkedCompressionInclusionData.word, mark] using mark_central alpha a g

@[simp] theorem inclusionData_word :
    (inclusionData alpha a hT).word = mark alpha a := rfl

/-- The short negative-corner contradiction for the general conceptual
construction.  A separated sign cuts to a nonzero corner on which the mark
tends to `-1`; Kazhdan transport makes its compression-defect square tend to
`1` in normalized Hilbert--Schmidt norm. -/
theorem negativeCorner_kazhdanTransport_contradiction
    (A : MarkedOpAlmostRepresentation (Extension alpha a) (mark alpha a)) :
    False := by
  rw [← inclusionData_word alpha a hT] at A
  exact KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation
    (inclusionData alpha a hT) A

theorem mark_eq_defect_sq :
    mark alpha a =
      ⁅(compressionCore alpha a hT).transported,
        (compressionCore alpha a hT).iota a⁆ ^ 2 := by
  exact commutator_conjugate_eq_commutator_sq_of_sq_eq_one
    _ _ (by simpa [compressionCore, KazhdanCompressionCore.transported,
      displaced] using displaced_sq alpha a)

theorem mark_mem_defectNormal :
    mark alpha a ∈ (compressionCore alpha a hT).defectNormal := by
  rw [mark_eq_defect_sq alpha a hT]
  exact (compressionCore alpha a hT).defectNormal.pow_mem
    ((compressionCore alpha a hT).defect_mem_defectNormal a) 2

/-- Finite presentability supplies countability without any extra hypothesis. -/
noncomputable def baseCountable : Countable Γ := by
  obtain ⟨n, eval, heval, -⟩ := Group.IsFinitelyPresented.out (G := Γ)
  letI : Countable (FreeGroup (Fin n)) := inferInstance
  exact heval.countable

noncomputable local instance : Countable Γ := baseCountable (Γ := Γ)

noncomputable local instance raw_countable : Countable (Raw Γ) :=
  Monoid.Coprod.mk_surjective.countable

noncomputable instance extension_countable : Countable (Extension alpha a) :=
  (QuotientGroup.mk'_surjective (relations alpha a)).countable

/-- Every homomorphism from the construction to a genuine norm-matrix
C*-corona kills the central Clifford sign. -/
theorem every_cstar_corona_hom_kills_mark
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : Extension alpha a →*
        unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      rho (mark alpha a) = 1 := by
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  let F := centralInvolutionSubgroup (mark alpha a) (mark_sq alpha a)
  letI : F.Normal := centralInvolutionSubgroup_normal
    (mark alpha a) (mark_sq alpha a) (mark_central alpha a)
  have hF : F ≤ (compressionCore alpha a hT).defectNormal :=
    (centralInvolutionSubgroup_le_iff_mem
      (mark alpha a) (mark_sq alpha a)
      (compressionCore alpha a hT).defectNormal).mpr
      (mark_mem_defectNormal alpha a hT)
  exact MonoidHom.mem_ker.mp
    ((compressionCore alpha a hT).finiteNormal_le_normMatrixCStarCoronaKernel
      F hF X hX rho
      (involution_mem_centralInvolutionSubgroup
        (mark alpha a) (mark_sq alpha a)))

/-- The Kazhdan--Clifford extension is unconditionally non-MF. -/
theorem not_isOperatorMF (ha : a ∉ Set.range alpha) :
    ¬ IsOperatorMF (Extension alpha a) := by
  simpa using (inclusionData alpha a hT).not_isOperatorMF
    (mark_ne_one alpha hAlpha a ha)

/-- **Kazhdan--Clifford construction (formal headline theorem).**  A
finitely presented Kazhdan group with a proper injective self-map produces a
finitely presented non-MF group.  The distinguished central involution is
nontrivial in the Clifford model and is killed by every norm-matrix-corona
representation. -/
theorem kazhdanCliffordConstruction
    (hTTextbook : HasKazhdanPropertyTComplex.{0, w} Γ)
    (ha : a ∉ Set.range alpha) :
    Group.IsFinitelyPresented (Extension alpha a) ∧
      Function.Injective (iota alpha a) ∧
      mark alpha a ≠ 1 ∧
      mark alpha a ^ 2 = 1 ∧
      (∀ g : Extension alpha a, Commute (mark alpha a) g) ∧
      (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
        let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
        letI : ∀ n, Nonempty (X n) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : Extension alpha a →*
            unitary (NormMatrixCStarCorona (fun n ↦ X n)),
          rho (mark alpha a) = 1) ∧
      ¬ IsCDEOperatorMF (Extension alpha a) := by
  let hTReal : HasKazhdanPropertyT.{0, 0} Γ :=
    hasKazhdanPropertyT_iff_textbook.mpr hTTextbook
  refine ⟨inferInstance, iota_injective alpha hAlpha a ha,
    mark_ne_one alpha hAlpha a ha, mark_sq alpha a, mark_central alpha a,
    ?_, ?_⟩
  · intro d hd
    exact every_cstar_corona_hom_kills_mark alpha a hTReal
      (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd)
  · rw [isCDEOperatorMF_iff_isOperatorMF]
    exact not_isOperatorMF alpha hAlpha a hTReal ha

end

end KazhdanCliffordConstruction
end GroupApproximation
