import GroupApproximation.Monsters.UniversalFinitelyPresentedTorsionFreeGroup

/-!
# The unconditional algebraic payload for the Hitchhiker monster

This is the source group consumed by the two-conjugacy-class embedding
construction.  The free factor supplies a faithful value for every nontrivial
finite-rank word, while the second factor contains every finitely presented
torsion-free group and carries a fixed nonidentity central element.

The direct product is enough: the two factors have independent jobs, and a
direct product preserves ordinary torsion-freeness without any normal-form
argument.
-/

namespace GroupApproximation.Monsters

/-- The completely explicit source of the group-theoretic part of the
Hitchhiker construction. -/
abbrev HitchhikerPayload : Type :=
  FreeGroup (Fin 2) × UniversalCentralizerPayload

instance hitchhikerPayload_countable : Countable HitchhikerPayload := by
  infer_instance

/-- The payload is ordinarily torsion-free. -/
theorem hitchhikerPayload_torsionFree :
    IsPowerTorsionFree HitchhikerPayload :=
  IsPowerTorsionFree.prod IsPowerTorsionFree.of_isMulTorsionFree
    universalCentralizerPayload_torsionFree

/-- The free rank-two word detector embeds as the first coordinate. -/
def freeTwoToHitchhikerPayload : FreeGroup (Fin 2) →* HitchhikerPayload where
  toFun g := (g, 1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem freeTwoToHitchhikerPayload_injective :
    Function.Injective freeTwoToHitchhikerPayload := by
  intro x y hxy
  exact congrArg Prod.fst hxy

/-- The universal centralizer carrier embeds as the second coordinate. -/
def universalCentralizerPayloadToHitchhikerPayload :
    UniversalCentralizerPayload →* HitchhikerPayload where
  toFun u := (1, u)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem universalCentralizerPayloadToHitchhikerPayload_injective :
    Function.Injective universalCentralizerPayloadToHitchhikerPayload := by
  intro x y hxy
  exact congrArg Prod.snd hxy

/-- The fixed element whose centralizer will be transported to every
nonidentity centralizer after conjugacy collapse. -/
def hitchhikerCentralizerElement : HitchhikerPayload :=
  (1, universalCentralizerElement)

theorem hitchhikerCentralizerElement_ne_one :
    hitchhikerCentralizerElement ≠ 1 := by
  intro h
  apply universalCentralizerElement_ne_one
  exact congrArg Prod.snd h

theorem hitchhikerCentralizerElement_mem_center :
    hitchhikerCentralizerElement ∈ Subgroup.center HitchhikerPayload := by
  rw [Subgroup.mem_center_iff]
  intro x
  apply Prod.ext
  · simp [hitchhikerCentralizerElement]
  · exact (Subgroup.mem_center_iff.mp
      universalCentralizerElement_mem_center x.2)

/-- Every finitely presented torsion-free group embeds in the explicit
Hitchhiker payload. -/
theorem embeds_hitchhikerPayload
    (G : Type) [Group G] [Group.IsFinitelyPresented G]
    (hG : IsPowerTorsionFree G) :
    ∃ f : G →* HitchhikerPayload, Function.Injective f := by
  obtain ⟨f, hf⟩ := embeds_universalCentralizerPayload G hG
  exact ⟨universalCentralizerPayloadToHitchhikerPayload.comp f,
    universalCentralizerPayloadToHitchhikerPayload_injective.comp hf⟩

/-- Free groups of every finite rank embed in the explicit payload. -/
theorem hitchhikerPayload_containsEveryFiniteRankFreeGroup :
    ContainsEveryFiniteRankFreeGroup HitchhikerPayload := by
  intro m
  obtain ⟨f, hf⟩ := embeds_freeGroup_universalCentralizerPayload m
  exact ⟨universalCentralizerPayloadToHitchhikerPayload.comp f,
    universalCentralizerPayloadToHitchhikerPayload_injective.comp hf⟩

/-- The unconditional source package, with no construction data or ambient
group as input. -/
theorem hitchhikerPayload_package :
    Countable HitchhikerPayload ∧
      IsPowerTorsionFree HitchhikerPayload ∧
      hitchhikerCentralizerElement ≠ 1 ∧
      hitchhikerCentralizerElement ∈ Subgroup.center HitchhikerPayload ∧
      ContainsEveryFiniteRankFreeGroup HitchhikerPayload ∧
      (∀ (G : Type) [Group G] [Group.IsFinitelyPresented G],
        IsPowerTorsionFree G →
        ∃ f : G →* HitchhikerPayload, Function.Injective f) := by
  exact ⟨inferInstance, hitchhikerPayload_torsionFree,
    hitchhikerCentralizerElement_ne_one,
    hitchhikerCentralizerElement_mem_center,
    hitchhikerPayload_containsEveryFiniteRankFreeGroup,
    embeds_hitchhikerPayload⟩

end GroupApproximation.Monsters
