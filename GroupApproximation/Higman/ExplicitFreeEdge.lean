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
noncomputable def sourceEquiv : FreeGroup X ≃* sourceSubgroup E :=
  (Subgroup.topEquiv (G := FreeGroup X)).symm.trans
    (Subgroup.equivMapOfInjective ⊤ E.source E.source_injective)

/-- The target subgroup is canonically a copy of the free group. -/
noncomputable def targetEquiv : FreeGroup X ≃* targetSubgroup E :=
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
noncomputable def edgeEquiv : sourceSubgroup E ≃* targetSubgroup E :=
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
  have h := equiv_eq_conj (φ := edgeEquiv E) (sourceElement E w)
  rw [coe_edgeEquiv_sourceElement] at h
  change of (E.target w) =
    t * of (((sourceEquiv E w : sourceSubgroup E) : G)) * t⁻¹ at h
  rw [coe_sourceEquiv] at h
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
  simpa [sigmaData] using stable_conj_source
    (sigmaData fixed t0 d hsource htarget) (FreeGroup.of (Sum.inl x))

/-- The resulting HNN relation `sigma t0 sigma⁻¹ = t0 d`. -/
theorem sigma_stable_conj_t0 (fixed : X → G) (t0 d : G)
    (hsource : Function.Injective (sigmaSource fixed t0))
    (htarget : Function.Injective (sigmaTarget fixed t0 d)) :
    (t : Extension (sigmaData fixed t0 d hsource htarget)) *
        of t0 * t⁻¹ = of (t0 * d) := by
  simpa [sigmaData] using stable_conj_source
    (sigmaData fixed t0 d hsource htarget) (FreeGroup.of (Sum.inr ()))

/-! ## The explicit `d` edge -/

variable {J : Type}

def dSource (k0 : G) (s tau : J → G) : FreeGroup (Unit ⊕ J) →* G :=
  FreeGroup.lift fun x ↦ x.elim (fun _ ↦ k0) (fun j ↦ s j * tau j)

def dTarget (k0 : G) (s : J → G) : FreeGroup (Unit ⊕ J) →* G :=
  FreeGroup.lift fun x ↦ x.elim (fun _ ↦ k0) s

@[simp] theorem dSource_k0 (k0 : G) (s tau : J → G) :
    dSource k0 s tau (FreeGroup.of (Sum.inl ())) = k0 := by simp [dSource]

@[simp] theorem dSource_payload (k0 : G) (s tau : J → G) (j : J) :
    dSource k0 s tau (FreeGroup.of (Sum.inr j)) = s j * tau j := by simp [dSource]

@[simp] theorem dTarget_k0 (k0 : G) (s : J → G) :
    dTarget k0 s (FreeGroup.of (Sum.inl ())) = k0 := by simp [dTarget]

@[simp] theorem dTarget_payload (k0 : G) (s : J → G) (j : J) :
    dTarget k0 s (FreeGroup.of (Sum.inr j)) = s j := by simp [dTarget]

/-- Concrete `d` edge data.  The two fields are exactly the freeness
obligations on the displayed tuples. -/
def dData (k0 : G) (s tau : J → G)
    (hsource : Function.Injective (dSource k0 s tau))
    (htarget : Function.Injective (dTarget k0 s)) : Data (Unit ⊕ J) G where
  source := dSource k0 s tau
  target := dTarget k0 s
  source_injective := hsource
  target_injective := htarget

theorem d_stable_conj_k0 (k0 : G) (s tau : J → G)
    (hsource : Function.Injective (dSource k0 s tau))
    (htarget : Function.Injective (dTarget k0 s)) :
    (t : Extension (dData k0 s tau hsource htarget)) * of k0 * t⁻¹ = of k0 := by
  simpa [dData] using stable_conj_source
    (dData k0 s tau hsource htarget) (FreeGroup.of (Sum.inl ()))

theorem d_stable_conj_payload (k0 : G) (s tau : J → G)
    (hsource : Function.Injective (dSource k0 s tau))
    (htarget : Function.Injective (dTarget k0 s)) (j : J) :
    (t : Extension (dData k0 s tau hsource htarget)) *
        of (s j * tau j) * t⁻¹ = of (s j) := by
  simpa [dData] using stable_conj_source
    (dData k0 s tau hsource htarget) (FreeGroup.of (Sum.inr j))

/-! ## A hypothesis-free Nielsen shear for a `tau` layer -/

def fixedInclusion : FreeGroup X →* FreeGroup (X ⊕ Unit) :=
  FreeGroup.lift (fun x ↦ FreeGroup.of (Sum.inl x))

def shearForward (payload : FreeGroup X) :
    FreeGroup (X ⊕ Unit) →* FreeGroup (X ⊕ Unit) :=
  FreeGroup.lift fun x ↦ x.elim (fun a ↦ FreeGroup.of (Sum.inl a))
    (fun _ ↦ FreeGroup.of (Sum.inr ()) * (fixedInclusion payload)⁻¹)

def shearBackward (payload : FreeGroup X) :
    FreeGroup (X ⊕ Unit) →* FreeGroup (X ⊕ Unit) :=
  FreeGroup.lift fun x ↦ x.elim (fun a ↦ FreeGroup.of (Sum.inl a))
    (fun _ ↦ FreeGroup.of (Sum.inr ()) * fixedInclusion payload)

@[simp] theorem shearForward_fixed (payload : FreeGroup X) (x : X) :
    shearForward payload (FreeGroup.of (Sum.inl x)) = FreeGroup.of (Sum.inl x) := by
  simp [shearForward]

@[simp] theorem shearBackward_fixed (payload : FreeGroup X) (x : X) :
    shearBackward payload (FreeGroup.of (Sum.inl x)) = FreeGroup.of (Sum.inl x) := by
  simp [shearBackward]

@[simp] theorem shearForward_k0 (payload : FreeGroup X) :
    shearForward payload (FreeGroup.of (Sum.inr ())) =
      FreeGroup.of (Sum.inr ()) * (fixedInclusion payload)⁻¹ := by
  simp [shearForward]

@[simp] theorem shearBackward_k0 (payload : FreeGroup X) :
    shearBackward payload (FreeGroup.of (Sum.inr ())) =
      FreeGroup.of (Sum.inr ()) * fixedInclusion payload := by
  simp [shearBackward]

theorem shearForward_comp_fixedInclusion (payload : FreeGroup X) :
    (shearForward payload).comp fixedInclusion = fixedInclusion := by
  apply FreeGroup.ext_hom
  intro x
  simp [fixedInclusion]

theorem shearBackward_comp_fixedInclusion (payload : FreeGroup X) :
    (shearBackward payload).comp fixedInclusion = fixedInclusion := by
  apply FreeGroup.ext_hom
  intro x
  simp [fixedInclusion]

theorem shearBackward_comp_shearForward (payload : FreeGroup X) :
    (shearBackward payload).comp (shearForward payload) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro x
  rcases x with x | _
  · simp
  · rename_i u
    rcases u with ⟨⟩
    rw [shearForward_k0, map_mul, map_inv, shearBackward_k0]
    have hfix := DFunLike.congr_fun
      (shearBackward_comp_fixedInclusion payload) payload
    change shearBackward payload (fixedInclusion payload) = fixedInclusion payload at hfix
    rw [hfix]
    group

theorem shearForward_comp_shearBackward (payload : FreeGroup X) :
    (shearForward payload).comp (shearBackward payload) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro x
  rcases x with x | _
  · simp
  · rename_i u
    rcases u with ⟨⟩
    rw [shearBackward_k0, map_mul, shearForward_k0]
    have hfix := DFunLike.congr_fun
      (shearForward_comp_fixedInclusion payload) payload
    change shearForward payload (fixedInclusion payload) = fixedInclusion payload at hfix
    rw [hfix]
    group

/-- The `tau`-layer shear is an actual automorphism, with no freeness input. -/
noncomputable def shearEquiv (payload : FreeGroup X) :
    FreeGroup (X ⊕ Unit) ≃* FreeGroup (X ⊕ Unit) :=
  MonoidHom.toMulEquiv (shearForward payload) (shearBackward payload)
    (shearBackward_comp_shearForward payload)
    (shearForward_comp_shearBackward payload)

noncomputable def shearData (payload : FreeGroup X) :
    Data (X ⊕ Unit) (FreeGroup (X ⊕ Unit)) where
  source := MonoidHom.id _
  target := (shearEquiv payload).toMonoidHom
  source_injective := Function.injective_id
  target_injective := (shearEquiv payload).injective

end ExplicitFreeEdge
end Higman
end GroupApproximation
