import GroupApproximation.Computability.ExactLiteralEFinInfSwitch
import GroupApproximation.Computability.PresentationCodes

/-!
# The exact event-cut ray switch for an arbitrary finite presentation

This is the seed-parametric semantic core of the `FIN`/`INF` switch.  The
finite presentation code `seed` supplies both the finite generator alphabet
and the relators copied at every vertex of the ray.  A false event identifies
adjacent copies generator by generator, while a true event kills its vertex.

Consequently an unbounded event set kills the entire group.  If the events
have a last cut, the killed head disappears and the uncut tail is exactly the
group presented by `seed`.  No approximation property and no particular seed
group enters the proof.
-/

namespace GroupApproximation
namespace ParametricFinInfSwitch

open ExactLiteralEFinInfSwitch
open PresentationCodes

noncomputable section

/-- The finite generator alphabet of the seed presentation. -/
abbrev SeedGenerator (seed : PresentationCode) := Fin (genCount seed)

/-- The countable stagewise alphabet of copies of the seed generators. -/
abbrev ParametricCopyGenerator (seed : PresentationCode) :=
  ℕ × SeedGenerator seed

/-- Embed a seed word into the copy at stage `j`. -/
def copyWord (seed : PresentationCode) (j : ℕ) :
    FreeGroup (SeedGenerator seed) →* FreeGroup (ParametricCopyGenerator seed) :=
  FreeGroup.map fun g ↦ (j, g)

/-- The relation identifying one seed generator across an uncut edge. -/
def bridgeWord (seed : PresentationCode) (j : ℕ) (g : SeedGenerator seed) :
    FreeGroup (ParametricCopyGenerator seed) :=
  FreeGroup.of (j, g) * (FreeGroup.of (j + 1, g))⁻¹

/-- The relation killing one seed generator at an event vertex. -/
def killWord (seed : PresentationCode) (j : ℕ) (g : SeedGenerator seed) :
    FreeGroup (ParametricCopyGenerator seed) :=
  FreeGroup.of (j, g)

/-- The event-cut ray presentation built from an arbitrary finite seed. -/
def parametricSwitchRelators (seed : PresentationCode) (E : StageEvents) :
    Set (FreeGroup (ParametricCopyGenerator seed)) :=
  {r | (∃ j s, s ∈ relatorFinset seed ∧ r = copyWord seed j s) ∨
    (∃ j g, E.event j = false ∧ r = bridgeWord seed j g) ∨
    (∃ j g, E.event j = true ∧ r = killWord seed j g)}

/-- The group presented by the seed-parametric event-cut ray. -/
abbrev ParametricSwitchGroup (seed : PresentationCode) (E : StageEvents) : Type :=
  PresentedGroup (parametricSwitchRelators seed E)

instance parametricSwitchGroup_countable (seed : PresentationCode)
    (E : StageEvents) : Countable (ParametricSwitchGroup seed E) := by
  unfold ParametricSwitchGroup PresentedGroup
  exact Function.Surjective.countable (QuotientGroup.mk'_surjective _)

theorem copyWord_mem (seed : PresentationCode) (E : StageEvents) (j : ℕ)
    {s : FreeGroup (SeedGenerator seed)} (hs : s ∈ relatorFinset seed) :
    copyWord seed j s ∈ parametricSwitchRelators seed E :=
  Or.inl ⟨j, s, hs, rfl⟩

theorem bridgeWord_mem (seed : PresentationCode) (E : StageEvents) (j : ℕ)
    (g : SeedGenerator seed) (hj : E.event j = false) :
    bridgeWord seed j g ∈ parametricSwitchRelators seed E :=
  Or.inr (Or.inl ⟨j, g, hj, rfl⟩)

theorem killWord_mem (seed : PresentationCode) (E : StageEvents) (j : ℕ)
    (g : SeedGenerator seed) (hj : E.event j = true) :
    killWord seed j g ∈ parametricSwitchRelators seed E :=
  Or.inr (Or.inr ⟨j, g, hj, rfl⟩)

/-- A false event literally identifies adjacent seed copies. -/
theorem of_eq_of_succ (seed : PresentationCode) (E : StageEvents) (j : ℕ)
    (g : SeedGenerator seed) (hj : E.event j = false) :
    (PresentedGroup.of (j, g) : ParametricSwitchGroup seed E) =
      PresentedGroup.of (j + 1, g) := by
  apply eq_of_mul_inv_eq_one
  exact PresentedGroup.one_of_mem (bridgeWord_mem seed E j g hj)

/-- A true event literally kills its vertex copy. -/
theorem of_eq_one_of_event (seed : PresentationCode) (E : StageEvents) (j : ℕ)
    (g : SeedGenerator seed) (hj : E.event j = true) :
    (PresentedGroup.of (j, g) : ParametricSwitchGroup seed E) = 1 := by
  exact PresentedGroup.one_of_mem (killWord_mem seed E j g hj)

/-- If an event occurs `d` stages later, the generator at the current stage
is already trivial. -/
theorem of_eq_one_of_event_after (seed : PresentationCode) (E : StageEvents)
    (g : SeedGenerator seed) :
    ∀ (d j : ℕ), E.event (j + d) = true →
      (PresentedGroup.of (j, g) : ParametricSwitchGroup seed E) = 1
  | 0, j, hj => of_eq_one_of_event seed E j g (by simpa using hj)
  | d + 1, j, hj => by
      cases hstage : E.event j with
      | false =>
          rw [of_eq_of_succ seed E j g hstage]
          apply of_eq_one_of_event_after seed E g d (j + 1)
          have hidx : (j + 1) + d = j + (d + 1) := by omega
          rw [hidx]
          exact hj
      | true => exact of_eq_one_of_event seed E j g hstage

/-- Under infinitely many events, every named generator dies. -/
theorem of_eq_one_of_infiniteEvents (seed : PresentationCode) (E : StageEvents)
    (hE : InfiniteEvents E) (j : ℕ) (g : SeedGenerator seed) :
    (PresentedGroup.of (j, g) : ParametricSwitchGroup seed E) = 1 := by
  obtain ⟨k, hjk, hk⟩ := hE j
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact of_eq_one_of_event_after seed E g d j hk

/-- The infinite-event branch is exactly the trivial group. -/
theorem subsingleton_of_infiniteEvents (seed : PresentationCode)
    (E : StageEvents) (hE : InfiniteEvents E) :
    Subsingleton (ParametricSwitchGroup seed E) := by
  have hle : Subgroup.closure
      (Set.range (PresentedGroup.of : ParametricCopyGenerator seed →
        ParametricSwitchGroup seed E)) ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨j, g⟩, rfl⟩
    exact Subgroup.mem_bot.mpr (of_eq_one_of_infiniteEvents seed E hE j g)
  have hbot : (⊥ : Subgroup (ParametricSwitchGroup seed E)) = ⊤ := by
    apply le_antisymm bot_le
    rw [← PresentedGroup.closure_range_of (parametricSwitchRelators seed E)]
    exact hle
  constructor
  intro x y
  apply eq_of_mul_inv_eq_one
  apply Subgroup.mem_bot.mp
  rw [hbot]
  exact Subgroup.mem_top _

/-- The infinite-event branch is explicitly isomorphic to the trivial group. -/
def equivPUnitOfInfiniteEvents (seed : PresentationCode) (E : StageEvents)
    (hE : InfiniteEvents E) : ParametricSwitchGroup seed E ≃* PUnit := by
  letI : Subsingleton (ParametricSwitchGroup seed E) :=
    subsingleton_of_infiniteEvents seed E hE
  let f : ParametricSwitchGroup seed E →* PUnit := 1
  exact MulEquiv.ofBijective f ⟨
    (fun _ _ _ ↦ Subsingleton.elim _ _),
    (fun y ↦ ⟨1, Subsingleton.elim _ y⟩)⟩

/-! ## The finite-event branch -/

/-- Generators at two stages connected only by false events are equal. -/
theorem of_eq_of_interval_false (seed : PresentationCode) (E : StageEvents)
    (g : SeedGenerator seed) :
    ∀ (d j : ℕ), (∀ k, j ≤ k → k < j + d → E.event k = false) →
      (PresentedGroup.of (j, g) : ParametricSwitchGroup seed E) =
        PresentedGroup.of (j + d, g)
  | 0, j, _ => by simp
  | d + 1, j, hfalse => by
      rw [of_eq_of_succ seed E j g (hfalse j (le_refl _) (by omega))]
      have hrest := of_eq_of_interval_false seed E g d (j + 1) (by
        intro k hjk hk
        apply hfalse k (by omega) (by omega))
      have hidx : (j + 1) + d = j + (d + 1) := by omega
      rw [hidx] at hrest
      exact hrest

/-- The canonical copy of the seed group at a chosen stage. -/
def stageHom (seed : PresentationCode) (E : StageEvents) (J : ℕ) :
    Carrier seed →* ParametricSwitchGroup seed E :=
  PresentedGroup.toGroup (f := fun g ↦ PresentedGroup.of (J, g)) (by
    intro r hr
    have hcomp :
        (PresentedGroup.mk (parametricSwitchRelators seed E)).comp
            (copyWord seed J) =
          FreeGroup.lift (fun g ↦
            (PresentedGroup.of (J, g) : ParametricSwitchGroup seed E)) := by
      apply FreeGroup.ext_hom
      intro g
      rfl
    rw [← hcomp, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (copyWord_mem seed E J hr))

@[simp] theorem stageHom_of (seed : PresentationCode) (E : StageEvents)
    (J : ℕ) (g : SeedGenerator seed) :
    stageHom seed E J (PresentedGroup.of g) = PresentedGroup.of (J, g) :=
  PresentedGroup.toGroup.of _

/-- Collapse every killed component to `1` and the tail beginning at `J` to
the seed group. -/
def collapseGenerator (seed : PresentationCode) (J : ℕ) :
    ParametricCopyGenerator seed → Carrier seed
  | (j, g) => if j < J then 1 else PresentedGroup.of g

theorem lift_collapse_copyWord (seed : PresentationCode) (J j : ℕ)
    (r : FreeGroup (SeedGenerator seed)) :
    FreeGroup.lift (collapseGenerator seed J) (copyWord seed j r) =
      if j < J then 1 else PresentedGroup.mk _ r := by
  by_cases hj : j < J
  · have hhom :
        (FreeGroup.lift (collapseGenerator seed J)).comp (copyWord seed j) = 1 := by
      apply FreeGroup.ext_hom
      intro g
      simp only [MonoidHom.comp_apply, copyWord, FreeGroup.map.of,
        FreeGroup.lift_apply_of, MonoidHom.one_apply]
      simp [collapseGenerator, hj]
    rw [← MonoidHom.comp_apply, hhom]
    simp [hj]
  · have hhom :
        (FreeGroup.lift (collapseGenerator seed J)).comp (copyWord seed j) =
          PresentedGroup.mk _ := by
      apply FreeGroup.ext_hom
      intro g
      simp only [MonoidHom.comp_apply, copyWord, FreeGroup.map.of,
        FreeGroup.lift_apply_of]
      change collapseGenerator seed J (j, g) = PresentedGroup.of g
      simp [collapseGenerator, hj]
    rw [← MonoidHom.comp_apply, hhom]
    simp [hj]

/-- The collapse map respects every switch relation at a canonical finite
cut. -/
theorem collapseGenerator_kills (seed : PresentationCode) (E : StageEvents)
    {J : ℕ} (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    ∀ r ∈ parametricSwitchRelators seed E,
      FreeGroup.lift (collapseGenerator seed J) r = 1 := by
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

/-- The quotient map from the ray to its surviving seed tail. -/
def collapseHom (seed : PresentationCode) (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    ParametricSwitchGroup seed E →* Carrier seed :=
  PresentedGroup.toGroup (collapseGenerator_kills seed E htail hhead)

@[simp] theorem collapseHom_of (seed : PresentationCode) (E : StageEvents)
    {J : ℕ} (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true)
    (j : ℕ) (g : SeedGenerator seed) :
    collapseHom seed E htail hhead
        (PresentedGroup.of (j, g)) =
      if j < J then 1 else PresentedGroup.of g :=
  PresentedGroup.toGroup.of _

theorem collapseHom_comp_stageHom (seed : PresentationCode) (E : StageEvents)
    {J : ℕ} (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    (collapseHom seed E htail hhead).comp (stageHom seed E J) =
      MonoidHom.id (Carrier seed) := by
  apply PresentedGroup.ext
  intro g
  simp [collapseHom_of, stageHom_of]

theorem stageHom_comp_collapseHom (seed : PresentationCode) (E : StageEvents)
    {J : ℕ} (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    (stageHom seed E J).comp (collapseHom seed E htail hhead) =
      MonoidHom.id (ParametricSwitchGroup seed E) := by
  apply PresentedGroup.ext
  rintro ⟨j, g⟩
  by_cases hj : j < J
  · rw [MonoidHom.comp_apply, collapseHom_of, if_pos hj, map_one,
      MonoidHom.id_apply]
    obtain ⟨k, hjk, hkJ, hk⟩ := hhead j hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    exact (of_eq_one_of_event_after seed E g d j hk).symm
  · rw [MonoidHom.comp_apply, collapseHom_of, if_neg hj, stageHom_of,
      MonoidHom.id_apply]
    have hjJ : J ≤ j := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjJ
    exact of_eq_of_interval_false seed E g d J (by
      intro k hkJ hk
      exact htail k hkJ)

/-- A canonical finite cut leaves exactly one copy of the seed group. -/
def equivSeedOfCut (seed : PresentationCode) (E : StageEvents) {J : ℕ}
    (htail : ∀ k, J ≤ k → E.event k = false)
    (hhead : ∀ j, j < J → ∃ k, j ≤ k ∧ k < J ∧ E.event k = true) :
    ParametricSwitchGroup seed E ≃* Carrier seed where
  toFun := collapseHom seed E htail hhead
  invFun := stageHom seed E J
  left_inv x := congrArg
    (fun f : ParametricSwitchGroup seed E →* ParametricSwitchGroup seed E ↦ f x)
    (stageHom_comp_collapseHom seed E htail hhead)
  right_inv x := congrArg (fun f : Carrier seed →* Carrier seed ↦ f x)
    (collapseHom_comp_stageHom seed E htail hhead)
  map_mul' := map_mul _

/-- The finite-event branch is exactly the group presented by `seed`. -/
theorem nonempty_equiv_seed_of_finiteEvents (seed : PresentationCode)
    (E : StageEvents) (hE : FiniteEvents E) :
    Nonempty (ParametricSwitchGroup seed E ≃* Carrier seed) := by
  obtain ⟨J, htail, hhead⟩ := hE
  exact ⟨equivSeedOfCut seed E htail hhead⟩

/-- The unconditional semantic dichotomy for an arbitrary finite seed. -/
theorem semantic_dichotomy (seed : PresentationCode) (E : StageEvents) :
    (InfiniteEvents E → Subsingleton (ParametricSwitchGroup seed E)) ∧
      (FiniteEvents E →
        Nonempty (ParametricSwitchGroup seed E ≃* Carrier seed)) :=
  ⟨subsingleton_of_infiniteEvents seed E,
    nonempty_equiv_seed_of_finiteEvents seed E⟩

/-- Every Boolean event stream has either arbitrarily late events or a
canonical final cut. -/
theorem events_dichotomy (E : StageEvents) :
    InfiniteEvents E ∨ FiniteEvents E := by
  classical
  by_cases hfinite : Set.Finite {j | E.event j = true}
  · apply Or.inr
    by_cases hempty : {j | E.event j = true} = ∅
    · refine ⟨0, ?_, ?_⟩
      · intro k _
        have hnot : E.event k ≠ true := by
          intro hk
          have hmem : k ∈ ({j | E.event j = true} : Set ℕ) := hk
          rw [hempty] at hmem
          exact hmem
        exact Bool.eq_false_of_not_eq_true hnot
      · intro j hj
        omega
    · have hnonempty : ({j | E.event j = true} : Set ℕ).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨last, hlast, hmax⟩ :=
        Set.exists_max_image {j | E.event j = true} id hfinite hnonempty
      refine ⟨last + 1, ?_, ?_⟩
      · intro k hk
        have hnot : E.event k ≠ true := by
          intro htrue
          have hkle : k ≤ last := hmax k htrue
          omega
        exact Bool.eq_false_of_not_eq_true hnot
      · intro j hj
        exact ⟨last, by omega, by omega, hlast⟩
  · apply Or.inl
    intro j
    have hinfinite : Set.Infinite {k | E.event k = true} := hfinite
    obtain ⟨k, hk, hjk⟩ := Set.Infinite.exists_gt hinfinite j
    exact ⟨k, Nat.le_of_lt hjk, hk⟩

/-- Every event stream produces exactly one of the two advertised group
isomorphism types: the trivial group or the seed group. -/
theorem two_isomorphism_types (seed : PresentationCode) (E : StageEvents) :
    (InfiniteEvents E ∧ Nonempty (ParametricSwitchGroup seed E ≃* PUnit)) ∨
      (FiniteEvents E ∧
        Nonempty (ParametricSwitchGroup seed E ≃* Carrier seed)) := by
  rcases events_dichotomy E with hInfinite | hFinite
  · exact Or.inl ⟨hInfinite, ⟨equivPUnitOfInfiniteEvents seed E hInfinite⟩⟩
  · exact Or.inr
      ⟨hFinite, nonempty_equiv_seed_of_finiteEvents seed E hFinite⟩

end

end ParametricFinInfSwitch
end GroupApproximation
