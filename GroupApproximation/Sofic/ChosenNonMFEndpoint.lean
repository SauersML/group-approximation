import GroupApproximation.Sofic.ChosenMarkedPresentation
import GroupApproximation.Sofic.MarkedCompressionInclusionData

/-!
# The Shalom-cover finitely presented marked-compression endpoint

This file connects the fully algebraic finite presentation to the analytic
marked-compression theorem.  Its vertex is the noncomputably chosen finitely
presented Kazhdan cover supplied in `ChosenMarkedPresentation`; this Lean
witness is not asserted to be the paper's displayed finite presentation.  All
group-theoretic input is proved here or in `ChosenMarkedPresentation`:

* the group is finitely presented and countable;
* its Kazhdan vertex has property `(T)`;
* the stable letter conjugates that vertex into itself;
* the root lamp centralizes the vertex; and
* the marked word is a nontrivial central involution.

The resulting `inclusionData` is the exact input consumed by the analytic
marked-compression theorem.  This file deliberately does not import that
theorem: the fully algebraic finite-presentation endpoint therefore remains
independently checkable and contains no analytic assumption.
-/

namespace GroupApproximation
namespace ChosenNonMFEndpoint

open ChosenMarkedPresentation

/-- The presented Shalom-cover witness group is countable. -/
noncomputable instance markedGroup_countable : Countable MarkedGroup :=
  (PresentedGroup.mk_surjective
    ((relators : Finset (FreeGroup Generator)) :
      Set (FreeGroup Generator))).countable

/-- The root lamp commutes with each displayed vertex generator. -/
theorem lamp_commutes_vertex_generator (i : Fin generatorCount) :
    Commute lamp (vertexMap (PresentedGroup.of i)) := by
  rw [vertexMap_generator]
  apply commutatorElement_eq_one_iff_commute.mp
  apply PresentedGroup.one_of_mem
  change commutatorWord lampLetter (vertexLetter i) ∈ relators
  simp [relators, lampRelators]

/-- The root lamp centralizes the whole Kazhdan vertex. -/
theorem lamp_commutes_vertex (x : Vertex) : Commute lamp (vertexMap x) := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective _ x
  induction w using FreeGroup.induction_on with
  | C1 => exact Commute.one_right _
  | of i =>
      rw [show PresentedGroup.mk _ (FreeGroup.of i) =
        PresentedGroup.of i from rfl]
      exact lamp_commutes_vertex_generator i
  | inv_of i hi =>
      rw [map_inv]
      exact hi.inv_right
  | mul a b ha hb =>
      simpa only [map_mul] using ha.mul_right hb

/-- The chosen omitted vertex maps to the displayed omitted base element. -/
theorem vertexMap_omittedVertex :
    vertexMap omittedVertex = wordInMarkedGroup omittedWord := by
  exact vertexMap_mk _

/-- The abstract presentation's `mark` is exactly the marked-compression word
used by the analytic interface. -/
theorem mark_eq_markedCompressionWord :
    mark = markedCompressionWord stable (vertexMap omittedVertex) lamp := by
  rw [vertexMap_omittedVertex]
  simp only [mark, markedWord, displacedLampWord, markedCompressionWord,
    commutatorElement_def, commutatorWord, map_mul, map_inv, omittedWord,
    stable, lamp]

/-- Exact one-sided marked-compression data carried by the finite
presentation. -/
noncomputable def inclusionData :
    MarkedCompressionInclusionData Vertex MarkedGroup where
  iota := vertexMap
  t := stable
  c := lamp
  a := omittedVertex
  kazhdan := vertex_hasKazhdanPropertyT
  compresses γ := by
    obtain ⟨δ, hδ⟩ := stable_conjugates_vertex_into_vertex γ
    exact ⟨δ, hδ.symm⟩
  comm_c := lamp_commutes_vertex
  word_sq := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_sq
  word_central g := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_central g

@[simp] theorem inclusionData_word : inclusionData.word = mark := by
  exact mark_eq_markedCompressionWord.symm

/-- The marked word in the analytic data is nontrivial. -/
theorem inclusionData_word_ne_one : inclusionData.word ≠ 1 := by
  rw [inclusionData_word]
  exact mark_ne_one

/-- **Top-level algebraic endpoint.**  The chosen Shalom-cover finite
presentation supplies nontrivial marked-compression inclusion data, exactly
in the form required by the analytic kill theorem. -/
theorem chosenFinitelyPresented_inclusionPackage :
    Group.IsFinitelyPresented MarkedGroup ∧
      Countable MarkedGroup ∧ inclusionData.word ≠ 1 := by
  exact ⟨inferInstance, inferInstance, inclusionData_word_ne_one⟩

end ChosenNonMFEndpoint
end GroupApproximation
