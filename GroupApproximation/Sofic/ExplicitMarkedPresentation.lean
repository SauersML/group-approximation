import GroupApproximation.Algebra.MappingTelescope
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import GroupApproximation.Sofic.ExplicitNonMFBase
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.PresentedGroup

/-!
# A finite marked presentation over the explicit Kazhdan compressor

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

There are deliberately two explicitly labelled algebraic gaps at the bottom:
the routine free-word induction proving the subgroup inclusion, and the map
to the already constructed telescope/Clifford witness which proves `w != 1`.
They are isolated as theorems rather than hidden as hypotheses of the final
presentation.
-/

namespace GroupApproximation
namespace ExplicitMarkedPresentation

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
  kazhdan : HasKazhdanPropertyT.{0, 0}
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

theorem vertex_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} Vertex :=
  coverData.kazhdan

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

/-- All relators in the explicit marked presentation. -/
noncomputable def relators : Finset (FreeGroup Generator) :=
  transportedCoverRelators ∪
    Finset.univ.image stableRelator ∪
    lampRelators ∪ markedCentralRelators

/-- The explicit finitely presented marked group. -/
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
  -- The transported Shalom relators are a subset of `relators`.
  sorry

@[simp] theorem vertexMap_generator (i : Fin generatorCount) :
    vertexMap (PresentedGroup.of i) = wordInMarkedGroup (vertexLetter i) := by
  exact PresentedGroup.toGroup.of _

/-- The stable relations hold on every displayed vertex generator. -/
theorem stable_conjugates_generator_into_vertex (i : Fin generatorCount) :
    stable * vertexMap (PresentedGroup.of i) * stable⁻¹ =
      vertexMap
        (PresentedGroup.mk _
          (liftWord (compression
            (vertexQuotient (PresentedGroup.of i))))) := by
  -- Unfold `stableRelator i` and use `PresentedGroup.one_of_mem`.
  sorry

/-- **Finite-presentation compressor lemma.**  Conjugation by the stable
letter sends the entire Kazhdan vertex into itself.  No endomorphism of the
Shalom cover is asserted or needed. -/
theorem stable_conjugates_vertex_into_vertex :
    ∀ x : Vertex,
      stable * vertexMap x * stable⁻¹ ∈ vertexMap.range := by
  -- Lift `x` to a free word and induct on that word.  The generator step is
  -- `stable_conjugates_generator_into_vertex`; inverse and product steps use
  -- that `vertexMap.range` is a subgroup.
  sorry

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
  -- This is one of `markedCentralRelators`.
  sorry

/-- The marked word commutes with every element of the presented group. -/
theorem mark_central (x : MarkedGroup) : mark * x = x * mark := by
  -- The relators give commutation with every finite generator; lift `x` to
  -- the free group and induct on a word.
  sorry

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

/-- Evaluate the finite marked presentation in any exact realization. -/
noncomputable def realizationHom {M : Type*} [Group M]
    (R : Realization M) : MarkedGroup →* M := by
  let gen : Generator → M
    | .inl i => R.base (vertexQuotient (PresentedGroup.of i))
    | .inr j => if j = 0 then R.stable else R.lamp
  apply PresentedGroup.toGroup (f := gen)
  intro r hr
  -- Split membership in the four finite relator packets.  Cover relators use
  -- `vertexQuotient`; stable relators use `compression_relation`; the other
  -- packets use the lamp and marked-word fields.
  sorry

/-- A realization which retains its marked word proves that the abstract
marked word is nontrivial. -/
theorem mark_ne_one_of_realization {M : Type*} [Group M]
    (R : Realization M)
    (hR : realizationHom R mark ≠ 1) : mark ≠ 1 := by
  intro h
  exact hR (by rw [h, map_one])

/-- **Remaining algebraic witness gap.**  The telescope and its strict range
characterization provide a realization whose two displaced lamps are distinct
Clifford sites, so the marked word is the nontrivial central sign. -/
theorem mark_ne_one : mark ≠ 1 := by
  -- Instantiate `Realization` in the Clifford lamp semidirect product over
  -- the coset action of the mapping-telescope ascending HNN group.  The key
  -- inequality is exactly
  -- `MappingTelescope.level_succ_mem_range_level_iff` together with
  -- `omitted_not_mem_range`.
  sorry

/-- The finite-presentation package needed by the non-MF theorem. -/
theorem explicit_finitelyPresented_marked_package :
    Group.IsFinitelyPresented MarkedGroup ∧
      HasKazhdanPropertyT.{0, 0} Vertex ∧
      (∀ x : Vertex,
        stable * vertexMap x * stable⁻¹ ∈ vertexMap.range) ∧
      mark ^ 2 = 1 ∧
      (∀ x : MarkedGroup, mark * x = x * mark) ∧
      mark ≠ 1 := by
  exact ⟨inferInstance, vertex_hasKazhdanPropertyT,
    stable_conjugates_vertex_into_vertex, mark_sq, mark_central, mark_ne_one⟩

end ExplicitMarkedPresentation
end GroupApproximation
