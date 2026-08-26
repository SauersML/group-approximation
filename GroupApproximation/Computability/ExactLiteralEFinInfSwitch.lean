import GroupApproximation.Sofic.LiteralNonMFPresentation

/-!
# The exact event-cut ray switch

This is the semantic core of the `FIN`/`INF` switch used by the fixed marked
query.  It contains no finite-presentation compiler and no literature input.

At vertex `j` the presentation has one copy of the literal marked group.  A
false event joins vertex `j` to vertex `j + 1` generator by generator, while a
true event kills vertex `j`.  Thus an unbounded set of true events kills every
component.  If the events have a last cut, all components before the cut die
and the remaining ray is exactly one copy of the literal group.
-/

namespace GroupApproximation
namespace ExactLiteralEFinInfSwitch

open LiteralNonMFPresentation

noncomputable section

/-- Stagewise event data.  Using `Bool` makes each individual stage decision
literal decidable data; uniform computability of a family of such streams is
a separate syntactic layer. -/
structure StageEvents where
  event : ℕ → Bool

/-- Events occur arbitrarily far out. -/
def InfiniteEvents (E : StageEvents) : Prop :=
  ∀ j, ∃ k, j ≤ k ∧ E.event k = true

/-- A canonical cut immediately after the last event.  For `J = 0` this also
covers the stream with no events.  When `J > 0`, the second clause says that
every vertex before `J` has an event between it and the cut; equivalently the
last event is at `J - 1`. -/
def FiniteEvents (E : StageEvents) : Prop :=
  ∃ J,
    (∀ k, J ≤ k → E.event k = false) ∧
    (∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true)

/-- The countable alphabet: a stage and one literal generator. -/
abbrev CopyGenerator := ℕ × Generator

/-- Embed a word into the copy at stage `j`. -/
def copyWord (j : ℕ) : FreeGroup Generator →* FreeGroup CopyGenerator :=
  FreeGroup.map fun g ↦ (j, g)

/-- The relation identifying one generator across an uncut edge. -/
def bridgeWord (j : ℕ) (g : Generator) : FreeGroup CopyGenerator :=
  FreeGroup.of (j, g) * (FreeGroup.of (j + 1, g))⁻¹

/-- The relation killing a generator at an event vertex. -/
def killWord (j : ℕ) (g : Generator) : FreeGroup CopyGenerator :=
  FreeGroup.of (j, g)

/-- The event-cut ray presentation. -/
def switchRelators (E : StageEvents) : Set (FreeGroup CopyGenerator) :=
  {r | (∃ j s, s ∈ relators ∧ r = copyWord j s) ∨
    (∃ j g, E.event j = false ∧ r = bridgeWord j g) ∨
    (∃ j g, E.event j = true ∧ r = killWord j g)}

/-- The group presented by the event-cut ray. -/
abbrev SwitchGroup (E : StageEvents) : Type :=
  PresentedGroup (switchRelators E)

instance switchGroup_countable (E : StageEvents) : Countable (SwitchGroup E) := by
  unfold SwitchGroup PresentedGroup
  exact Function.Surjective.countable (QuotientGroup.mk'_surjective _)

theorem copyWord_mem (E : StageEvents) (j : ℕ) {s : FreeGroup Generator}
    (hs : s ∈ relators) : copyWord j s ∈ switchRelators E :=
  Or.inl ⟨j, s, hs, rfl⟩

theorem bridgeWord_mem (E : StageEvents) (j : ℕ) (g : Generator)
    (hj : E.event j = false) : bridgeWord j g ∈ switchRelators E :=
  Or.inr (Or.inl ⟨j, g, hj, rfl⟩)

theorem killWord_mem (E : StageEvents) (j : ℕ) (g : Generator)
    (hj : E.event j = true) : killWord j g ∈ switchRelators E :=
  Or.inr (Or.inr ⟨j, g, hj, rfl⟩)

/-- A false event literally identifies adjacent copies. -/
theorem of_eq_of_succ (E : StageEvents) (j : ℕ) (g : Generator)
    (hj : E.event j = false) :
    (PresentedGroup.of (j, g) : SwitchGroup E) = PresentedGroup.of (j + 1, g) := by
  apply eq_of_mul_inv_eq_one
  exact PresentedGroup.one_of_mem (bridgeWord_mem E j g hj)

/-- A true event literally kills its vertex copy. -/
theorem of_eq_one_of_event (E : StageEvents) (j : ℕ) (g : Generator)
    (hj : E.event j = true) :
    (PresentedGroup.of (j, g) : SwitchGroup E) = 1 := by
  exact PresentedGroup.one_of_mem (killWord_mem E j g hj)

/-- If some event occurs `d` stages later, the generator at the current stage
is already trivial.  The proof walks toward that event, using a bridge exactly
at the false stages it crosses. -/
theorem of_eq_one_of_event_after (E : StageEvents) (g : Generator) :
    ∀ (d j : ℕ), E.event (j + d) = true →
      (PresentedGroup.of (j, g) : SwitchGroup E) = 1
  | 0, j, hj => of_eq_one_of_event E j g (by simpa using hj)
  | d + 1, j, hj => by
      cases hstage : E.event j with
      | false =>
          rw [of_eq_of_succ E j g hstage]
          apply of_eq_one_of_event_after E g d (j + 1)
          have hidx : (j + 1) + d = j + (d + 1) := by omega
          rw [hidx]
          exact hj
      | true => exact of_eq_one_of_event E j g hstage

/-- Under infinitely many events, every named generator dies. -/
theorem of_eq_one_of_infiniteEvents (E : StageEvents) (hE : InfiniteEvents E)
    (j : ℕ) (g : Generator) :
    (PresentedGroup.of (j, g) : SwitchGroup E) = 1 := by
  obtain ⟨k, hjk, hk⟩ := hE j
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact of_eq_one_of_event_after E g d j hk

/-- The infinite-event branch is exactly the trivial group. -/
theorem subsingleton_of_infiniteEvents (E : StageEvents)
    (hE : InfiniteEvents E) : Subsingleton (SwitchGroup E) := by
  have hle : Subgroup.closure
      (Set.range (PresentedGroup.of : CopyGenerator → SwitchGroup E)) ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨j, g⟩, rfl⟩
    exact Subgroup.mem_bot.mpr (of_eq_one_of_infiniteEvents E hE j g)
  have hbot : (⊥ : Subgroup (SwitchGroup E)) = ⊤ := by
    apply le_antisymm bot_le
    rw [← PresentedGroup.closure_range_of (switchRelators E)]
    exact hle
  constructor
  intro x y
  apply eq_of_mul_inv_eq_one
  apply Subgroup.mem_bot.mp
  rw [hbot]
  exact Subgroup.mem_top _

/-! ## The finite-event branch -/

/-- Generators at two stages connected only by false events are equal. -/
theorem of_eq_of_interval_false (E : StageEvents) (g : Generator) :
    ∀ (d j : ℕ), (∀ k, j ≤ k → k < j + d → E.event k = false) →
      (PresentedGroup.of (j, g) : SwitchGroup E) = PresentedGroup.of (j + d, g)
  | 0, j, _ => by simp
  | d + 1, j, hfalse => by
      rw [of_eq_of_succ E j g (hfalse j (le_refl _) (by omega))]
      have hrest := of_eq_of_interval_false E g d (j + 1) (by
        intro k hjk hk
        apply hfalse k (by omega) (by omega))
      have hidx : (j + 1) + d = j + (d + 1) := by omega
      rw [hidx] at hrest
      exact hrest

/-- The canonical copy of the literal group at a chosen stage. -/
def stageHom (E : StageEvents) (J : ℕ) : MarkedGroup →* SwitchGroup E :=
  PresentedGroup.toGroup (f := fun g ↦ PresentedGroup.of (J, g)) (by
    intro r hr
    have hcomp :
        (PresentedGroup.mk (switchRelators E)).comp (copyWord J) =
          FreeGroup.lift (fun g ↦ (PresentedGroup.of (J, g) : SwitchGroup E)) := by
      apply FreeGroup.ext_hom
      intro g
      rfl
    rw [← hcomp, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (copyWord_mem E J hr))

@[simp] theorem stageHom_of (E : StageEvents) (J : ℕ) (g : Generator) :
    stageHom E J (PresentedGroup.of g) = PresentedGroup.of (J, g) :=
  PresentedGroup.toGroup.of _

/-- Collapse every killed component to `1` and the tail beginning at `J` to
the literal group. -/
def collapseGenerator (J : ℕ) : CopyGenerator → MarkedGroup
  | (j, g) => if j < J then 1 else PresentedGroup.of g

theorem lift_collapse_copyWord (J j : ℕ) (r : FreeGroup Generator) :
    FreeGroup.lift (collapseGenerator J) (copyWord j r) =
      if j < J then 1 else wordInMarkedGroup r := by
  by_cases hj : j < J
  · have hhom : (FreeGroup.lift (collapseGenerator J)).comp (copyWord j) = 1 := by
      apply FreeGroup.ext_hom
      intro g
      simp only [MonoidHom.comp_apply, copyWord, FreeGroup.map.of,
        FreeGroup.lift_apply_of, MonoidHom.one_apply]
      simp [collapseGenerator, hj]
    rw [← MonoidHom.comp_apply, hhom]
    simp [hj]
  · have hhom : (FreeGroup.lift (collapseGenerator J)).comp (copyWord j) =
        wordInMarkedGroup := by
      apply FreeGroup.ext_hom
      intro g
      simp only [MonoidHom.comp_apply, copyWord, FreeGroup.map.of,
        FreeGroup.lift_apply_of]
      change collapseGenerator J (j, g) = PresentedGroup.of g
      simp [collapseGenerator, hj]
    rw [← MonoidHom.comp_apply, hhom]
    simp [hj]

/-- The collapse map respects every switch relation at a canonical finite
cut. -/
theorem collapseGenerator_kills (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    ∀ r ∈ switchRelators E, FreeGroup.lift (collapseGenerator J) r = 1 := by
  intro r hr
  rcases hr with ⟨j, s, hs, rfl⟩ | ⟨j, g, hj, rfl⟩ | ⟨j, g, hj, rfl⟩
  · rw [lift_collapse_copyWord]
    split_ifs with h
    · rfl
    · exact PresentedGroup.one_of_mem hs
  · simp only [bridgeWord, map_mul, map_inv, FreeGroup.lift_apply_of]
    by_cases hjJ : j < J
    · have hsucc : j + 1 < J := by
        by_contra hn
        have heq : j + 1 = J := by omega
        obtain ⟨k, hjk, hkJ, hk⟩ := hhead j hjJ
        have hkj : k = j := by omega
        exact Bool.noConfusion (hj.symm.trans (hkj ▸ hk))
      simp [collapseGenerator, hjJ, hsucc]
    · have hjge : J ≤ j := by omega
      have hsge : ¬ j + 1 < J := by omega
      simp [collapseGenerator, hjJ, hsge]
  · have hjJ : j < J := by
      by_contra hn
      exact Bool.noConfusion ((htail j (by omega)).symm.trans hj)
    simp [killWord, collapseGenerator, hjJ]

/-- The quotient map from the ray to its surviving literal tail. -/
def collapseHom (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    SwitchGroup E →* MarkedGroup :=
  PresentedGroup.toGroup (collapseGenerator_kills E htail hhead)

@[simp] theorem collapseHom_of (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true)
    (j : ℕ) (g : Generator) :
    collapseHom E htail hhead (PresentedGroup.of (j, g)) =
      if j < J then 1 else PresentedGroup.of g :=
  PresentedGroup.toGroup.of _

theorem collapseHom_comp_stageHom (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    (collapseHom E htail hhead).comp (stageHom E J) = MonoidHom.id MarkedGroup := by
  apply PresentedGroup.ext
  intro g
  simp [collapseHom_of, stageHom_of]

theorem stageHom_comp_collapseHom (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    (stageHom E J).comp (collapseHom E htail hhead) = MonoidHom.id (SwitchGroup E) := by
  apply PresentedGroup.ext
  rintro ⟨j, g⟩
  by_cases hj : j < J
  · rw [MonoidHom.comp_apply, collapseHom_of, if_pos hj, map_one, MonoidHom.id_apply]
    obtain ⟨k, hjk, hkJ, hk⟩ := hhead j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    exact (of_eq_one_of_event_after E g d j hk).symm
    · rw [MonoidHom.comp_apply, collapseHom_of, if_neg hj, stageHom_of,
      MonoidHom.id_apply]
    have hjJ : J ≤ j := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjJ
    exact of_eq_of_interval_false E g d J (by
      intro k hkJ hk
      exact htail k hkJ)

/-- A canonical finite cut leaves exactly one copy of the literal group. -/
def equivLiteralOfCut (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    SwitchGroup E ≃* MarkedGroup where
  toFun := collapseHom E htail hhead
  invFun := stageHom E J
  left_inv x := congrArg (fun f : SwitchGroup E →* SwitchGroup E ↦ f x)
    (stageHom_comp_collapseHom E htail hhead)
  right_inv x := congrArg (fun f : MarkedGroup →* MarkedGroup ↦ f x)
    (collapseHom_comp_stageHom E htail hhead)
  map_mul' := map_mul _

/-- The finite-event branch is exactly the literal non-MF group. -/
theorem nonempty_equiv_literal_of_finiteEvents (E : StageEvents)
    (hE : FiniteEvents E) : Nonempty (SwitchGroup E ≃* MarkedGroup) := by
  obtain ⟨J, htail, hhead⟩ := hE
  exact ⟨equivLiteralOfCut E htail hhead⟩

/-- The unconditional semantic dichotomy of the switch. -/
theorem semantic_dichotomy (E : StageEvents) :
    (InfiniteEvents E → Subsingleton (SwitchGroup E)) ∧
      (FiniteEvents E → Nonempty (SwitchGroup E ≃* MarkedGroup)) :=
  ⟨subsingleton_of_infiniteEvents E, nonempty_equiv_literal_of_finiteEvents E⟩

end

end ExactLiteralEFinInfSwitch
end GroupApproximation
