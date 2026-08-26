import GroupApproximation.Higman.ConjugatedDetector

/-!
# Explicit free associated subgroups for HNN compiler layers

The `d` and `sigma` layers in an Aanderaa-style tower are HNN extensions
between two explicitly generated free subgroups.  This file provides the
honest Lean data behind that sentence.  It does not assume an embedding
theorem or any fact from the literature: two maps out of a free group and
proofs that those particular maps are injective determine the associated
subgroups, their equivalence, the HNN extension, and its generator relations.

The last section spells out the `sigma` edge

    fixed generators |-> fixed generators,
    t0               |-> t0 * d.

Thus a future concrete compiler has a precise obligation: prove injectivity
of the two displayed free-group evaluation maps in its already constructed
base.  There is no opaque "the edge groups are free" premise.
-/

namespace GroupApproximation
namespace Higman
namespace ExplicitFreeEdge

open HNNExtension

variable {X G : Type} [Group G]

/-- Two explicitly embedded copies of the same free group in `G`. -/
structure Data (X G : Type) [Group G] where
  source : FreeGroup X →* G
  target : FreeGroup X →* G
  source_injective : Function.Injective source
  target_injective : Function.Injective target

variable (E : Data X G)

/-- The source associated subgroup. -/
def sourceSubgroup : Subgroup G :=
  (⊤ : Subgroup (FreeGroup X)).map E.source

/-- The target associated subgroup. -/
def targetSubgroup : Subgroup G :=
  (⊤ : Subgroup (FreeGroup X)).map E.target

/-- The source subgroup is canonically a copy of the free group. -/
noncomputable def sourceEquiv : FreeGroup X ≣* sourceSubgroup E :=
  (Subgroup.topEquiv (G := FreeGroup X)).symm.trans
    (Subgroup.equivMapOfInjective ⊤ E.source E.source_injective)

/-- The target subgroup is canonically a copy of the free group. -/
noncomputable def targetEquiv : FreeGroup X ≣* targetSubgroup E :=
  (Subgroup.topEquiv (G := FreeGroup X)).symm.trans
    (Subgroup.equivMapOfInjective ⊤ E.target E.target_injective)

theorem coe_sourceEquiv (w : FreeGroup X) :
    ((sourceEquiv E w : sourceSubgroup E) : G) = E.source w := by
  show ((Subgroup.equivMapOfInjective ⊤ E.source E.source_injective
    ((Subgroup.topEquiv (G := FreeGroup X)).symm w) : G)) = _
  rw [Subgroup.coe_equivMapOfInjective_apply]
  rfl

theorem coe_targetEquiv (w : FreeGroup X) :
    ((targetEquiv E w : targetSubgroup E) : G) = E.target w := by
  show ((Subgroup.equivMapOfInjective ⊤ E.target E.target_injective
    ((Subgroup.topEquiv (G := FreeGroup X)).symm w) : G)) = _
  rw [Subgroup.coe_equivMapOfInjective_apply]
  rfl

/-- The associated-subgroup equivalence induced by using the same free word
on the source and target generators. -/
noncomputable def edgeEquiv : sourceSubgroup E ≣* targetSubgroup E :=
  (sourceEquiv E).symm.trans (targetEquiv E)

/-- A free word regarded as an element of the source edge subgroup. -/
noncomputable def sourceElement (w : FreeGroup X) : sourceSubgroup E :=
  sourceEquiv E w

/-- The edge equivalence evaluates the same free word on the target tuple. -/
theorem coe_edgeEquiv_sourceElement (w : FreeGroup X) :
    ((edgeEquiv E (sourceElement E w) : targetSubgroup E) : G) = E.target w := by
  change ((targetEquiv E ((sourceEquiv E).symm (sourceEquiv E w)) :
    targetSubgroup E) : G) = _
  rw [MulEquiv.symm_apply_apply, coe_targetEquiv]

/-- The honest HNN extension determined by the two free edge embeddings. -/
abbrev Extension : Type :=
  HNNExtension G (sourceSubgroup E) (targetSubgroup E) (edgeEquiv E)

/-- The stable letter carries source evaluation of every free word to target
evaluation of the same word. -/
theorem stable_conj_source (w : FreeGroup X) :
    (t : Extension E) * of (E.source w) * t⁻¹ = of (E.target w) := by
  have h := equiv_eq_conj (edgeEquiv E) (sourceElement E w)
  rw [coe_edgeEquiv_sourceElement, coe_sourceEquiv] at h
  exact h.symm

/-! ## The explicit `sigma` edge -/

/-- The source evaluation for fixed generators together with `t0`. -/
def sigmaSource (fixed : X → G) (t0 : G) : FreeGroup (X ⊕ Unit) →* G :=
  FreeGroup.lift fun x ↦ x.elim fixed (fun _ ↦ t0)

/-- The target evaluation fixes the old generators and replaces `t0` by
`t0 * d`. -/
def sigmaTarget (fixed : X → G) (t0 d : G) : FreeGroup (X ⊕ Unit) →* G :=
  FreeGroup.lift fun x ↦ x.elim fixed (fun _ ↦ t0 * d)

@[simp] theorem sigmaSource_fixed (fixed : X → G) (t0 : G) (x : X) :
    sigmaSource fixed t0 (FreeGroup.of (Sum.inl x)) = fixed x := by
  simp [sigmaSource]

@[simp] theorem sigmaSource_t0 (fixed : X → G) (t0 : G) :
    sigmaSource fixed t0 (FreeGroup.of (Sum.inr ())) = t0 := by
  simp [sigmaSource]

@[simp] theorem sigmaTarget_fixed (fixed : X → G) (t0 d : G) (x : X) :
    sigmaTarget fixed t0 d (FreeGroup.of (Sum.inl x)) = fixed x := by
  simp [sigmaTarget]

@[simp] theorem sigmaTarget_t0 (fixed : X → G) (t0 d : G) :
    sigmaTarget fixed t0 d (FreeGroup.of (Sum.inr ())) = t0 * d := by
  simp [sigmaTarget]

/-- Concrete edge data for the `sigma` layer, once the two explicit
evaluation maps have been proved injective in the preceding tower. -/
def sigmaData (fixed : X → G) (t0 d : G)
    (hsource : Function.Injective (sigmaSource fixed t0))
    (htarget : Function.Injective (sigmaTarget fixed t0 d)) :
    Data (X ⊕ Unit) G where
  source := sigmaSource fixed t0
  target := sigmaTarget fixed t0 d
  source_injective := hsource
  target_injective := htarget

/-- The resulting HNN relation on each fixed generator. -/
theorem sigma_stable_conj_fixed (fixed : X → G) (t0 d : G)
    (hsource : Function.Injective (sigmaSource fixed t0))
    (htarget : Function.Injective (sigmaTarget fixed t0 d)) (x : X) :
    (t : Extension (sigmaData fixed t0 d hsource htarget)) *
        of (fixed x) * t⁻¹ = of (fixed x) := by
  simpa using stable_conj_source
    (sigmaData fixed t0 d hsource htarget) (FreeGroup.of (Sum.inl x))

/-- The resulting HNN relation `sigma t0 sigma⁻¹ = t0 d`. -/
theorem sigma_stable_conj_t0 (fixed : X → G) (t0 d : G)
    (hsource : Function.Injective (sigmaSource fixed t0))
    (htarget : Function.Injective (sigmaTarget fixed t0 d)) :
    (t : Extension (sigmaData fixed t0 d hsource htarget)) *
        of t0 * t⁻¹ = of (t0 * d) := by
  simpa using stable_conj_source
    (sigmaData fixed t0 d hsource htarget) (FreeGroup.of (Sum.inr ()))

end ExplicitFreeEdge
end Higman
end GroupApproximation
