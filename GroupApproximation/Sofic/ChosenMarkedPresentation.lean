import GroupApproximation.Algebra.MappingTelescope
import GroupApproximation.Algebra.PresentedGroupEvaluation
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import GroupApproximation.Kazhdan.KazhdanUniverseDescent
import GroupApproximation.Sofic.ExplicitNonMFBase
import GroupApproximation.Sofic.MarkedCompressionExplicitGroup
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup

/-!
# A chosen finite marked presentation over the explicit Kazhdan compressor

This file removes the finite-presentation bottleneck from the marked non-MF
construction.  The explicit compressor group itself is only known here to be
finitely generated.  Shalom's theorem supplies a finitely presented Kazhdan
cover `Delta -> Gamma`.  We do **not** try to lift the compressor to an
endomorphism of `Delta`.  Instead, for each generator `s_i` of `Delta`, we
choose one word `b_i` mapping to `alpha(q(s_i))` and impose the finitely many
relations

`t s_i t^-1 = b_i`.

They imply the only fact used by the analytic obstruction:

`t Delta t^-1 <= Delta`.

The presentation then adjoins one involution `c`, centralizes it against the
Kazhdan vertex, and makes the marked commutator

`w = [t c t^-1, a (t c t^-1) a^-1]`

a central involution.  All relation sets below are genuinely finite.

The free-word induction proving the subgroup inclusion and the map to the
already constructed telescope/Clifford witness are both carried out below.
Thus `w != 1` is proved from the concrete realization rather than accepted as
a hypothesis of the final presentation.
-/

namespace GroupApproximation
namespace ChosenMarkedPresentation

open ExplicitNonMFBase

/-! ## The Shalom cover -/

/-- The concrete data returned by the presentation form of Shalom's theorem. -/
structure CoverData where
  n : ℕ
  rels : Finset (FreeGroup (Fin n))
  quotient :
    PresentedGroup ((rels : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) →* Base
  quotient_surjective : Function.Surjective quotient
  kazhdan : HasKazhdanPropertyT.{0, 1}
    (PresentedGroup ((rels : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))))

/-- Existence of a finitely presented property-`(T)` cover, packaged so that
`Classical.choice` (rather than forbidden elimination from `Exists` into
data) can fix one below. -/
theorem coverData_nonempty : Nonempty CoverData := by
  classical
  obtain ⟨S, -, -, hS⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset
      Base base_hasKazhdanPropertyT
  obtain ⟨n, rels, q, hq, hT⟩ :=
    Shalom.exists_presented_kazhdan_cover S hS base_hasKazhdanPropertyT
  exact ⟨⟨n, rels, q, hq, hT⟩⟩

/-- A fixed finitely presented property-`(T)` cover of the explicit base. -/
noncomputable def coverData : CoverData :=
  Classical.choice coverData_nonempty

/-- Number of generators in the chosen Kazhdan cover. -/
noncomputable abbrev generatorCount : ℕ := coverData.n

/-- Relators in the chosen Kazhdan cover. -/
noncomputable abbrev coverRelators :
    Finset (FreeGroup (Fin generatorCount)) := coverData.rels

/-- The finitely presented Kazhdan vertex group. -/
noncomputable abbrev Vertex : Type :=
  PresentedGroup ((coverRelators : Finset (FreeGroup (Fin generatorCount))) :
    Set (FreeGroup (Fin generatorCount)))

/-- The quotient from the presented vertex onto the explicit compressor base. -/
noncomputable abbrev vertexQuotient : Vertex →* Base := coverData.quotient

theorem vertexQuotient_surjective : Function.Surjective vertexQuotient :=
  coverData.quotient_surjective

theorem vertex_hasKazhdanPropertyT_universeOne :
    HasKazhdanPropertyT.{0, 1} Vertex :=
  coverData.kazhdan

theorem vertex_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} Vertex :=
  HasKazhdanPropertyT.of_max.{0, 1, 0} coverData.kazhdan

instance vertex_finitelyPresented : Group.IsFinitelyPresented Vertex :=
  inferInstance

/-! ## Raw word lifts and the finite marked presentation -/

/-- The composite free-word evaluation onto the explicit base. -/
noncomputable def freeToBase : FreeGroup (Fin generatorCount) →* Base :=
  vertexQuotient.comp (PresentedGroup.mk _)

theorem freeToBase_surjective : Function.Surjective freeToBase :=
  vertexQuotient_surjective.comp (PresentedGroup.mk_surjective _)

/-- A chosen raw word above each element of the explicit base. -/
noncomputable def liftWord (g : Base) : FreeGroup (Fin generatorCount) :=
  Function.surjInv freeToBase_surjective g

@[simp] theorem freeToBase_liftWord (g : Base) :
    freeToBase (liftWord g) = g :=
  Function.surjInv_eq freeToBase_surjective g

/-- Generators of the final finite presentation.  `Fin 2` holds the stable
letter and the lamp; using a sum avoids generating executable code from the
noncomputably chosen number `generatorCount`. -/
noncomputable abbrev Generator := Fin generatorCount ⊕ Fin 2

noncomputable abbrev Generator.vertex (i : Fin generatorCount) : Generator :=
  Sum.inl i

noncomputable abbrev Generator.stable : Generator := Sum.inr 0

noncomputable abbrev Generator.lamp : Generator := Sum.inr 1

/-- Embed a word in the vertex generators into the final free group. -/
noncomputable def embedVertexWord :
    FreeGroup (Fin generatorCount) →* FreeGroup Generator :=
  FreeGroup.lift (fun i ↦ FreeGroup.of (Generator.vertex i))

noncomputable abbrev vertexLetter (i : Fin generatorCount) :
    FreeGroup Generator := FreeGroup.of (Generator.vertex i)

noncomputable abbrev stableLetter : FreeGroup Generator :=
  FreeGroup.of Generator.stable

noncomputable abbrev lampLetter : FreeGroup Generator :=
  FreeGroup.of Generator.lamp

/-- Commutator word, using the convention `[x,y]=xyx^-1y^-1`. -/
def commutatorWord {X : Type*} [Group X] (x y : X) : X :=
  x * y * x⁻¹ * y⁻¹

/-- The universal map from a presented group computes by free evaluation on
each represented word. -/
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

/-- Evaluation commutes with embedding a vertex word. -/
theorem lift_embedVertexWord {M : Type*} [Group M]
    (f : Generator → M) (w : FreeGroup (Fin generatorCount)) :
    FreeGroup.lift f (embedVertexWord w) =
      FreeGroup.lift (fun i ↦ f (Generator.vertex i)) w := by
  change ((FreeGroup.lift f).comp embedVertexWord) w =
    FreeGroup.lift (fun i ↦ f (Generator.vertex i)) w
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [embedVertexWord]

/-- A raw word representing the chosen lift of the omitted base element. -/
noncomputable def omittedWord : FreeGroup Generator :=
  embedVertexWord (liftWord omitted)

/-- The conjugated lamp `d=tct^-1`. -/
noncomputable def displacedLampWord : FreeGroup Generator :=
  stableLetter * lampLetter * stableLetter⁻¹

/-- The marked commutator. -/
noncomputable def markedWord : FreeGroup Generator :=
  commutatorWord displacedLampWord
    (omittedWord * displacedLampWord * omittedWord⁻¹)

/-- A chosen word above `compression(q(s_i))`. -/
noncomputable def compressedGeneratorWord (i : Fin generatorCount) :
    FreeGroup Generator :=
  embedVertexWord
    (liftWord (compression (vertexQuotient (PresentedGroup.of i))))

/-- The stable-letter relation for the `i`th vertex generator. -/
noncomputable def stableRelator (i : Fin generatorCount) :
    FreeGroup Generator :=
  stableLetter * vertexLetter i * stableLetter⁻¹ *
    (compressedGeneratorWord i)⁻¹

/-- Original relators, transported from the Shalom cover. -/
noncomputable def transportedCoverRelators : Finset (FreeGroup Generator) :=
  coverRelators.image embedVertexWord

/-- The finite list making the lamp an involution centralizing the vertex. -/
noncomputable def lampRelators : Finset (FreeGroup Generator) :=
  {lampLetter ^ 2} ∪
    Finset.univ.image (fun i : Fin generatorCount ↦
      commutatorWord lampLetter (vertexLetter i))

/-- The finite list making the marked word a central involution. -/
noncomputable def markedCentralRelators : Finset (FreeGroup Generator) :=
  {markedWord ^ 2,
    commutatorWord markedWord stableLetter,
    commutatorWord markedWord lampLetter} ∪
    Finset.univ.image (fun i : Fin generatorCount ↦
      commutatorWord markedWord (vertexLetter i))

/-- All relators in the chosen marked presentation. -/
noncomputable def relators : Finset (FreeGroup Generator) :=
  transportedCoverRelators ∪
    Finset.univ.image stableRelator ∪
    lampRelators ∪ markedCentralRelators

/-- The chosen finitely presented marked group. -/
noncomputable abbrev MarkedGroup : Type :=
  PresentedGroup ((relators : Finset (FreeGroup Generator)) :
    Set (FreeGroup Generator))

instance markedGroup_finitelyPresented :
    Group.IsFinitelyPresented MarkedGroup := inferInstance

/-- Evaluation of raw presentation words in the marked group. -/
noncomputable abbrev wordInMarkedGroup :
    FreeGroup Generator →* MarkedGroup :=
  PresentedGroup.mk
    ((relators : Finset (FreeGroup Generator)) : Set (FreeGroup Generator))

/-- Stable letter in the marked group. -/
noncomputable abbrev stable : MarkedGroup := wordInMarkedGroup stableLetter

/-- Root lamp in the marked group. -/
noncomputable abbrev lamp : MarkedGroup := wordInMarkedGroup lampLetter

/-- The marked central involution in the marked group. -/
noncomputable abbrev mark : MarkedGroup := wordInMarkedGroup markedWord

/-- The chosen lift of the omitted element in the vertex group. -/
noncomputable def omittedVertex : Vertex :=
  PresentedGroup.mk _ (liftWord omitted)

@[simp] theorem omittedVertex_maps_to_omitted :
    vertexQuotient omittedVertex = omitted := by
  exact freeToBase_liftWord omitted

/-! ## The vertex homomorphism and its finite consequences -/

/-- The canonical homomorphism from the Kazhdan cover to the marked group. -/
noncomputable def vertexMap : Vertex →* MarkedGroup := by
  apply PresentedGroup.toGroup
    (f := fun i : Fin generatorCount ↦
      wordInMarkedGroup (vertexLetter i))
  intro r hr
  rw [← lift_embedVertexWord
    (f := fun j : Generator ↦ wordInMarkedGroup (FreeGroup.of j))]
  rw [freeGroup_lift_presentedGroup_generators]
  apply PresentedGroup.one_of_mem
  change embedVertexWord r ∈ relators
  simp only [relators, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl
    (Finset.mem_image.mpr ⟨r, Finset.mem_coe.mp hr, rfl⟩)))

@[simp] theorem vertexMap_generator (i : Fin generatorCount) :
    vertexMap (PresentedGroup.of i) = wordInMarkedGroup (vertexLetter i) := by
  exact PresentedGroup.toGroup.of _

/-- The vertex map computes on every represented free word by embedding that
word into the final presentation. -/
theorem vertexMap_mk (w : FreeGroup (Fin generatorCount)) :
    vertexMap (PresentedGroup.mk _ w) =
      wordInMarkedGroup (embedVertexWord w) := by
  change PresentedGroup.toGroup _ (PresentedGroup.mk _ w) = _
  rw [presentedToGroup_mk]
  rw [← lift_embedVertexWord
    (f := fun j : Generator ↦ wordInMarkedGroup (FreeGroup.of j))]
  rw [freeGroup_lift_presentedGroup_generators]

/-- The stable relations hold on every displayed vertex generator. -/
theorem stable_conjugates_generator_into_vertex (i : Fin generatorCount) :
    stable * vertexMap (PresentedGroup.of i) * stable⁻¹ =
      vertexMap
        (PresentedGroup.mk _
          (liftWord (compression
            (vertexQuotient (PresentedGroup.of i))))) := by
  rw [vertexMap_generator, vertexMap_mk]
  have hrel : wordInMarkedGroup (stableRelator i) = 1 := by
    apply PresentedGroup.one_of_mem
    change stableRelator i ∈ relators
    simp only [relators, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩)))
  simp only [stableRelator, map_mul, map_inv] at hrel
  exact mul_inv_eq_one.mp hrel

/-- **Finite-presentation compressor lemma.**  Conjugation by the stable
letter sends the entire Kazhdan vertex into itself.  No endomorphism of the
Shalom cover is asserted or needed. -/
theorem stable_conjugates_vertex_into_vertex :
    ∀ x : Vertex,
      stable * vertexMap x * stable⁻¹ ∈ vertexMap.range := by
  intro x
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp
  | of i =>
      rw [show PresentedGroup.mk _ (FreeGroup.of i) =
        PresentedGroup.of i from rfl]
      exact ⟨PresentedGroup.mk _
        (liftWord (compression (vertexQuotient (PresentedGroup.of i)))),
        (stable_conjugates_generator_into_vertex i).symm⟩
  | inv_of i hi =>
      have hinv := vertexMap.range.inv_mem hi
      rw [map_inv]
      have heq :
          stable * (vertexMap (PresentedGroup.mk _ (FreeGroup.of i)))⁻¹ *
              stable⁻¹ =
            (stable * vertexMap (PresentedGroup.mk _ (FreeGroup.of i)) *
              stable⁻¹)⁻¹ := by group
      exact (congrArg (fun z : MarkedGroup ↦ z ∈ vertexMap.range) heq).mpr hinv
  | mul a b ha hb =>
      rw [map_mul]
      rw [map_mul vertexMap]
      have hmul := vertexMap.range.mul_mem ha hb
      have heq :
          stable *
              (vertexMap (PresentedGroup.mk _ a) *
                vertexMap (PresentedGroup.mk _ b)) * stable⁻¹ =
            (stable * vertexMap (PresentedGroup.mk _ a) * stable⁻¹) *
              (stable * vertexMap (PresentedGroup.mk _ b) * stable⁻¹) := by
        group
      exact (congrArg (fun z : MarkedGroup ↦ z ∈ vertexMap.range) heq).mpr hmul

/-- The Kazhdan subgroup used by the analytic obstruction is the range of
`vertexMap`. -/
noncomputable def kazhdanVertex : Subgroup MarkedGroup := vertexMap.range

theorem stable_conjugates_kazhdanVertex :
    ∀ x : kazhdanVertex,
      stable * (x : MarkedGroup) * stable⁻¹ ∈ kazhdanVertex := by
  rintro ⟨x, y, rfl⟩
  exact stable_conjugates_vertex_into_vertex y

/-- The marked word is an involution in the presented group. -/
theorem mark_sq : mark ^ 2 = 1 := by
  apply PresentedGroup.one_of_mem
  change markedWord ^ 2 ∈ relators
  simp [relators, markedCentralRelators]

/-- The marked word commutes with every element of the presented group. -/
theorem mark_central (x : MarkedGroup) : mark * x = x * mark := by
  have hgen : ∀ j : Generator,
      mark * wordInMarkedGroup (FreeGroup.of j) =
        wordInMarkedGroup (FreeGroup.of j) * mark := by
    intro j
    have hcomm : wordInMarkedGroup
        (commutatorWord markedWord (FreeGroup.of j)) = 1 := by
      apply PresentedGroup.one_of_mem
      change commutatorWord markedWord (FreeGroup.of j) ∈ relators
      rcases j with i | j
      · simp [relators, markedCentralRelators, vertexLetter]
      · fin_cases j <;>
          simp [relators, markedCentralRelators, stableLetter, lampLetter]
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of i => exact hgen i
  | inv_of i hi =>
      have hswap : wordInMarkedGroup (FreeGroup.of i) * mark =
          mark * wordInMarkedGroup (FreeGroup.of i) := hi.symm
      calc
        mark * (wordInMarkedGroup (FreeGroup.of i))⁻¹ =
            (wordInMarkedGroup (FreeGroup.of i))⁻¹ *
              (wordInMarkedGroup (FreeGroup.of i) * mark) *
              (wordInMarkedGroup (FreeGroup.of i))⁻¹ := by group
        _ = (wordInMarkedGroup (FreeGroup.of i))⁻¹ *
              (mark * wordInMarkedGroup (FreeGroup.of i)) *
              (wordInMarkedGroup (FreeGroup.of i))⁻¹ := by rw [hswap]
        _ = (wordInMarkedGroup (FreeGroup.of i))⁻¹ * mark := by group
  | mul a b ha hb =>
      rw [map_mul]
      calc
        mark * (wordInMarkedGroup a * wordInMarkedGroup b) =
            (mark * wordInMarkedGroup a) * wordInMarkedGroup b := by group
        _ = (wordInMarkedGroup a * mark) * wordInMarkedGroup b := by rw [ha]
        _ = wordInMarkedGroup a * (mark * wordInMarkedGroup b) := by group
        _ = wordInMarkedGroup a * (wordInMarkedGroup b * mark) := by rw [hb]
        _ = (wordInMarkedGroup a * wordInMarkedGroup b) * mark := by group

/-! ## Realization interface

The next structure is the exact universal-property interface used to map the
finite presentation to the genuine telescope/Clifford model.  It contains no
approximation hypotheses.  A downstream file constructs an inhabitant from
`MappingTelescope` and the two-site Clifford witness.
-/

/-- Exact target data sufficient to realize every defining relation. -/
structure Realization (M : Type*) [Group M] where
  base : Base →* M
  stable : M
  lamp : M
  compression_relation : ∀ g : Base,
    stable * base g * stable⁻¹ = base (compression g)
  lamp_sq : lamp ^ 2 = 1
  lamp_centralizes_base : ∀ g : Base,
    commutatorWord lamp (base g) = 1
  marked_sq :
    (commutatorWord
      (stable * lamp * stable⁻¹)
      (base omitted * (stable * lamp * stable⁻¹) * (base omitted)⁻¹)) ^ 2 = 1
  marked_central : ∀ x : M,
    commutatorWord
      (commutatorWord
        (stable * lamp * stable⁻¹)
        (base omitted * (stable * lamp * stable⁻¹) * (base omitted)⁻¹)) x = 1

/-- Evaluation of the finite generating alphabet in a realization. -/
noncomputable def realizationGenerator {M : Type*} [Group M]
    (R : Realization M) : Generator → M
  | .inl i => R.base (vertexQuotient (PresentedGroup.of i))
  | .inr j => if j = 0 then R.stable else R.lamp

@[simp] theorem realizationGenerator_vertex {M : Type*} [Group M]
    (R : Realization M) (i : Fin generatorCount) :
    realizationGenerator R (Generator.vertex i) =
      R.base (vertexQuotient (PresentedGroup.of i)) := rfl

@[simp] theorem realizationGenerator_stable {M : Type*} [Group M]
    (R : Realization M) :
    realizationGenerator R Generator.stable = R.stable := by
  simp [realizationGenerator]

@[simp] theorem realizationGenerator_lamp {M : Type*} [Group M]
    (R : Realization M) :
    realizationGenerator R Generator.lamp = R.lamp := by
  simp [realizationGenerator]

/-- Embedded vertex words evaluate through the quotient to the base. -/
theorem realization_eval_vertex {M : Type*} [Group M]
    (R : Realization M) (w : FreeGroup (Fin generatorCount)) :
    FreeGroup.lift (realizationGenerator R) (embedVertexWord w) =
      R.base (freeToBase w) := by
  rw [lift_embedVertexWord]
  change (FreeGroup.lift fun i ↦
      R.base (vertexQuotient (PresentedGroup.of i))) w =
    R.base (freeToBase w)
  change (FreeGroup.lift fun i ↦
      R.base (vertexQuotient (PresentedGroup.of i))) w =
    (R.base.comp freeToBase) w
  apply freeGroup_hom_eq_on_generators
  intro i
  rw [FreeGroup.lift_apply_of, MonoidHom.comp_apply]
  change R.base (vertexQuotient (PresentedGroup.of i)) =
    R.base (freeToBase (FreeGroup.of i))
  rw [freeToBase, MonoidHom.comp_apply]
  rfl

@[simp] theorem realization_eval_omitted {M : Type*} [Group M]
    (R : Realization M) :
    FreeGroup.lift (realizationGenerator R) omittedWord = R.base omitted := by
  rw [omittedWord, realization_eval_vertex, freeToBase_liftWord]

@[simp] theorem realization_eval_displaced {M : Type*} [Group M]
    (R : Realization M) :
    FreeGroup.lift (realizationGenerator R) displacedLampWord =
      R.stable * R.lamp * R.stable⁻¹ := by
  simp [displacedLampWord]

@[simp] theorem realization_eval_marked {M : Type*} [Group M]
    (R : Realization M) :
    FreeGroup.lift (realizationGenerator R) markedWord =
      commutatorWord
        (R.stable * R.lamp * R.stable⁻¹)
        (R.base omitted * (R.stable * R.lamp * R.stable⁻¹) *
          (R.base omitted)⁻¹) := by
  simp [markedWord, commutatorWord]

/-- Evaluate the finite marked presentation in any exact realization. -/
noncomputable def realizationHom {M : Type*} [Group M]
    (R : Realization M) : MarkedGroup →* M := by
  apply PresentedGroup.toGroup (f := realizationGenerator R)
  intro r hr
  change r ∈ relators at hr
  simp only [relators, Finset.mem_union] at hr
  rcases hr with ((hr | hr) | hr) | hr
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    rw [realization_eval_vertex]
    change R.base (vertexQuotient (PresentedGroup.mk _ q)) = 1
    rw [PresentedGroup.one_of_mem (Finset.mem_coe.mpr hq), map_one, map_one]
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    simp only [stableRelator, map_mul, map_inv]
    rw [show FreeGroup.lift (realizationGenerator R) stableLetter =
        R.stable by simp [stableLetter],
      show FreeGroup.lift (realizationGenerator R) (vertexLetter i) =
        R.base (vertexQuotient (PresentedGroup.of i)) by simp [vertexLetter],
      show FreeGroup.lift (realizationGenerator R)
          (compressedGeneratorWord i) =
        R.base (compression (vertexQuotient (PresentedGroup.of i))) by
          rw [compressedGeneratorWord, realization_eval_vertex,
            freeToBase_liftWord]]
    exact mul_inv_eq_one.mpr (R.compression_relation _)
  · simp only [lampRelators, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image] at hr
    rcases hr with rfl | ⟨i, -, rfl⟩
    · simpa using R.lamp_sq
    · simpa [commutatorWord] using
        R.lamp_centralizes_base
          (vertexQuotient (PresentedGroup.of i))
  · simp only [markedCentralRelators, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hr
    rcases hr with (rfl | (rfl | rfl)) | ⟨i, -, rfl⟩
    · simpa using R.marked_sq
    · simpa [commutatorWord] using R.marked_central R.stable
    · simpa [commutatorWord] using R.marked_central R.lamp
    · simpa [commutatorWord] using
        R.marked_central (R.base (vertexQuotient (PresentedGroup.of i)))

@[simp] theorem realizationHom_mark {M : Type*} [Group M]
    (R : Realization M) :
    realizationHom R mark =
      commutatorWord
        (R.stable * R.lamp * R.stable⁻¹)
        (R.base omitted * (R.stable * R.lamp * R.stable⁻¹) *
          (R.base omitted)⁻¹) := by
  change PresentedGroup.toGroup _
      (PresentedGroup.mk _ markedWord) = _
  rw [presentedToGroup_mk, realization_eval_marked]

/-- A realization which retains its marked word proves that the abstract
marked word is nontrivial. -/
theorem mark_ne_one_of_realization {M : Type*} [Group M]
    (R : Realization M)
    (hR : realizationHom R mark ≠ 1) : mark ≠ 1 := by
  intro h
  exact hR (by rw [h, map_one])

/-- The telescope and its strict range characterization provide a realization
whose two displaced lamps are distinct Clifford sites, so the marked word is
the nontrivial central sign. -/
theorem mark_ne_one : mark ≠ 1 := by
  let R : Realization MarkedCompression.Explicit.theGroup := {
    base := MarkedCompression.Explicit.theIota
    stable := MarkedCompression.Explicit.theT
    lamp := MarkedCompression.Explicit.theC
    compression_relation := MarkedCompression.Explicit.theCompress
    lamp_sq := MarkedCompression.Explicit.theCSq
    lamp_centralizes_base := by
      intro g
      exact commutatorElement_eq_one_iff_commute.mpr
        (MarkedCompression.Explicit.theCommC g)
    marked_sq := MarkedCompression.Explicit.theWordSq
    marked_central := by
      intro x
      exact commutatorElement_eq_one_iff_commute.mpr
        (MarkedCompression.Explicit.theWordCentral x)
  }
  apply mark_ne_one_of_realization R
  rw [realizationHom_mark]
  exact MarkedCompression.Explicit.theWordNeOne

/-- The finite-presentation package needed by the non-MF theorem. -/
theorem chosenFinitelyPresented_markedPackage :
    Group.IsFinitelyPresented MarkedGroup ∧
      HasKazhdanPropertyT.{0, 0} Vertex ∧
      (∀ x : Vertex,
        stable * vertexMap x * stable⁻¹ ∈ vertexMap.range) ∧
      mark ^ 2 = 1 ∧
      (∀ x : MarkedGroup, mark * x = x * mark) ∧
      mark ≠ 1 := by
  exact ⟨inferInstance, vertex_hasKazhdanPropertyT,
    stable_conjugates_vertex_into_vertex, mark_sq, mark_central, mark_ne_one⟩

end ChosenMarkedPresentation
end GroupApproximation
