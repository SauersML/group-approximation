import GroupApproximation.Sofic.SingleDefectSaturation

/-!
# Saturation without surjectivity: the defect is a normal closure downstairs

`SingleDefectSaturation` reduced the router's obligation from *defect
surjectivity* to *one saturated element*, but it kept a second field,
`quotient_surjective`, and used it for exactly one purpose: to know that the
image `⟪[s, ι(P)]⟫.map q` of the **upstairs** defect is a normal subgroup of the
target, so that a normal closure could be compared against it.

That detour is avoidable, and this file removes it.  The compression defect of
the *pushed* source is by definition a normal closure **in the target**, so it
is normal there for free, and the comparison goes through with no hypothesis on
`q` at all.

## What this buys

A router no longer has to produce a quotient *of the source*.  Any homomorphism
`q : E →* Q` into any nontrivial `Q` whatsoever, whose value at the one marked
commutator normally generates `Q`, already forces the whole compression defect
of the pushed core to be `Q`.

Surjectivity is **dropped, not derived**: the normal closure of `q w` can be all
of `Q` while `q` misses most of it --- `ℤ ↠ ⟨x⟩ ≤ A₅` at a three-cycle `x`
normally generates `A₅` and is very far from onto.  What the argument shows is
that the analytic endpoint never needed the image of the upstairs defect in the
first place, only a normal Kazhdan subgroup of the target sitting inside the
target's own defect.

## The three pieces

* `BareDefectSourceData.pushAmbient` --- transport of a compression source along
  an **arbitrary** homomorphism.  `BareDefectSourceData.mapAmbient` is the
  special case where injectivity is used to re-prove the one clause that is not
  automatic, `witness_commutator_ne_one`; here that clause is supplied directly,
  which is what lets the map be non-injective and non-surjective.
* `BareDefectSourceData.pushAmbient_defectNormal_eq_top` --- the
  surjectivity-free saturation theorem.  Unconditional: no router, and no
  hypothesis on `q` beyond the saturation equation itself.
* `SaturatingRouterData` --- `SingleDefectRouterData` with
  `quotient_surjective` deleted, and its composite to the frozen endpoint.
  `SingleDefectRouterData.toSaturatingRouterData` certifies that this interface
  assumes strictly less, so every consumer of the old one is covered.

## What this does *not* buy

Nothing here constructs a router, and no theorem below is unconditional in the
router.  Declarations that consume `SaturatingRouterData` carry
`_of_saturatingRouter` in their names for the same reason `_of_bareRoutingData`
is part of the frozen endpoint's name: the interface is a hypothesis, and none
of them may be cited as an unconditional existence theorem.  What has changed is
only that the hypothesis is now strictly weaker than the one the arithmetic
construction was previously asked for.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

/-! ## 1.  Transport of a compression source along an arbitrary homomorphism -/

namespace BareDefectSourceData

variable {P : Type} {E : Type u} [Group P] [Group E]

/-- **Transport along an arbitrary homomorphism.**

Every clause of `BareDefectSourceData` except the last is an *equation* between
words in the data, so it is preserved by any homomorphism.  The last clause,
`witness_commutator_ne_one`, is an inequation and is the only one that can fail;
here it is taken as an argument rather than re-proved from injectivity.

`BareDefectSourceData.mapAmbient f hf` is this construction with the argument
supplied by injectivity of `f`. -/
def pushAmbient (D : BareDefectSourceData P E) {Q : Type v} [Group Q]
    (q : E →* Q) (hne : ⁅q D.s, q (D.iota D.witness)⁆ ≠ 1) :
    BareDefectSourceData P Q where
  iota := q.comp D.iota
  u := q D.u
  s := q D.s
  kazhdan := D.kazhdan
  compresses := by
    intro p
    obtain ⟨r, hr⟩ := D.compresses p
    exact ⟨r, by simpa using congrArg q hr⟩
  commutesAfterCompression := by
    intro p
    simpa using (D.commutesAfterCompression p).map q
  witness := D.witness
  witness_commutator_ne_one := hne

@[simp] theorem pushAmbient_s (D : BareDefectSourceData P E) {Q : Type v}
    [Group Q] (q : E →* Q) (hne : ⁅q D.s, q (D.iota D.witness)⁆ ≠ 1) :
    (D.pushAmbient q hne).s = q D.s := rfl

@[simp] theorem pushAmbient_iota (D : BareDefectSourceData P E) {Q : Type v}
    [Group Q] (q : E →* Q) (hne : ⁅q D.s, q (D.iota D.witness)⁆ ≠ 1) :
    (D.pushAmbient q hne).iota = q.comp D.iota := rfl

@[simp] theorem pushAmbient_witness (D : BareDefectSourceData P E)
    {Q : Type v} [Group Q] (q : E →* Q)
    (hne : ⁅q D.s, q (D.iota D.witness)⁆ ≠ 1) :
    (D.pushAmbient q hne).witness = D.witness := rfl

/-- The marked commutator of a pushed source is the image of the marked
commutator.  Both sides unfold to `⁅q s, q (ι w)⁆` once the transported root is
rewritten to the protected element. -/
theorem markedCommutator_pushAmbient (D : BareDefectSourceData P E)
    {Q : Type v} [Group Q] (q : E →* Q)
    (hne : ⁅q D.s, q (D.iota D.witness)⁆ ≠ 1) :
    SingleDefectSaturation.markedCommutator (D.pushAmbient q hne) =
      q (SingleDefectSaturation.markedCommutator D) := by
  rw [SingleDefectSaturation.markedCommutator_eq,
    SingleDefectSaturation.markedCommutator_eq, map_commutatorElement]
  rfl

/-- **One saturated element makes the pushed defect everything, with no
hypothesis on the map.**

The compression defect of the pushed source is a normal closure *in `Q`*, so it
is normal in `Q` by construction rather than by transport, and the marked
commutator's image is one of its generators.  A normal subgroup containing an
element contains that element's normal closure, which is `⊤`.

This is the statement
`SingleDefectSaturation.defectNormal_map_eq_top_of_saturating_element` wanted,
with `Function.Surjective q` deleted: surjectivity was needed there only to make
the *image* of the upstairs defect normal, and the image never has to be
formed. -/
theorem pushAmbient_defectNormal_eq_top (D : BareDefectSourceData P E)
    {Q : Type v} [Group Q] (q : E →* Q)
    (hne : ⁅q D.s, q (D.iota D.witness)⁆ ≠ 1)
    (hsat : Subgroup.normalClosure
      ({q (SingleDefectSaturation.markedCommutator D)} : Set Q) = ⊤) :
    (D.pushAmbient q hne).core.defectNormal = ⊤ := by
  apply top_unique
  rw [← hsat]
  refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
  rw [← markedCommutator_pushAmbient D q hne]
  exact SingleDefectSaturation.markedCommutator_mem_defectNormal _

end BareDefectSourceData

/-! ## 2.  The routing interface with `quotient_surjective` deleted -/

namespace PushedDefectSaturation

open SingleDefectSaturation

/-- **`SingleDefectRouterData` minus surjectivity.**

Field for field this is `SingleDefectSaturation.SingleDefectRouterData` with
`quotient_surjective` removed.  `SingleDefectRouterData.toSaturatingRouterData`
below is the forgetful map, so this interface is strictly weaker and every
router that produced the old one produces this one.

This structure is a **hypothesis**, not a theorem.  Nothing in this file
constructs an inhabitant. -/
structure SaturatingRouterData {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) where
  /-- The target group.  Not required to be a quotient of the source. -/
  Quotient : Type
  [groupQuotient : Group Quotient]
  /-- The map from the source.  No surjectivity is asked of it. -/
  quotient : E →* Quotient
  /-- The target is finitely presented. -/
  [finitelyPresented : Group.IsFinitelyPresented Quotient]
  /-- The target is nontrivial. -/
  [nontrivial : Nontrivial Quotient]
  /-- Property `(T)` of the target. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Quotient
  /-- Torsion-freeness of the target, in power form. -/
  torsionFree : IsPowerTorsionFree Quotient
  /-- First generator produced by the routing stage. -/
  generatorOne : Quotient
  /-- Second generator produced by the routing stage. -/
  generatorTwo : Quotient
  /-- The two routed elements generate the target. -/
  generates :
    Subgroup.closure ({generatorOne, generatorTwo} : Set Quotient) = ⊤
  /-- **The single-defect clause**, unchanged. -/
  saturates :
    Subgroup.normalClosure
      ({quotient (markedCommutator D)} : Set Quotient) = ⊤

namespace SaturatingRouterData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : BareDefectSourceData P E} (R : SaturatingRouterData.{u} D)

local instance saturatingQuotientGroup : Group R.Quotient := R.groupQuotient
local instance saturatingQuotientNontrivial : Nontrivial R.Quotient :=
  R.nontrivial
local instance saturatingQuotientFinitelyPresented :
    Group.IsFinitelyPresented R.Quotient := R.finitelyPresented

/-- **The routed marked commutator is nontrivial.**  Were it trivial its normal
closure would be `⊥`, and `saturates` would make `⊥ = ⊤` in a nontrivial group.
This is `SingleDefectRouterData.marked_ne_one`, which never used surjectivity
either. -/
theorem marked_ne_one : R.quotient (markedCommutator D) ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (1 : R.Quotient)
  apply hx
  have hle : Subgroup.normalClosure
      ({R.quotient (markedCommutator D)} : Set R.Quotient) ≤ ⊥ :=
    Subgroup.normalClosure_le_normal
      (Set.singleton_subset_iff.mpr (Subgroup.mem_bot.mpr h))
  have hmem : x ∈ Subgroup.normalClosure
      ({R.quotient (markedCommutator D)} : Set R.Quotient) := by
    rw [R.saturates]
    exact Subgroup.mem_top x
  exact Subgroup.mem_bot.mp (hle hmem)

/-- The commutator clause for the pushed source, in the shape `pushAmbient`
asks for. -/
theorem pushed_commutator_ne_one :
    ⁅R.quotient D.s, R.quotient (D.iota D.witness)⁆ ≠ 1 := by
  have h := R.marked_ne_one
  rwa [markedCommutator_eq, map_commutatorElement] at h

/-- **The pushed compression source**, living on the target group. -/
def pushedSource : BareDefectSourceData P R.Quotient :=
  D.pushAmbient R.quotient R.pushed_commutator_ne_one

/-- The pushed compression defect is the whole target. -/
theorem pushedSource_defectNormal_eq_top :
    R.pushedSource.core.defectNormal = ⊤ :=
  BareDefectSourceData.pushAmbient_defectNormal_eq_top D R.quotient
    R.pushed_commutator_ne_one R.saturates

/-- The protected element survives in the target: a commutator with a trivial
left entry is trivial. -/
theorem protected_ne_one : R.quotient D.s ≠ 1 := by
  intro h
  apply R.pushed_commutator_ne_one
  rw [h]
  simp

/-- **The frozen routing interface, at the pushed source.**

The routing map is the identity of the target: the source has already been moved
there.  `defect_surjective` is then `Subgroup.map_id` applied to the saturation
theorem, and nothing has to be assumed about `R.quotient`. -/
def toBareRoutingData : BareRoutingData R.pushedSource where
  Quotient := R.Quotient
  quotient := MonoidHom.id R.Quotient
  kazhdan := R.kazhdan
  torsionFree := R.torsionFree
  generatorOne := R.generatorOne
  generatorTwo := R.generatorTwo
  generates := R.generates
  defect_surjective := by
    rw [Subgroup.map_id]
    exact R.pushedSource_defectNormal_eq_top
  protected_ne_one := R.protected_ne_one

end SaturatingRouterData

/-- **`SingleDefectRouterData` is the stronger interface.**  Forgetting
`quotient_surjective` is the whole map, so any router producing the old datum
produces the new one and every consumer below applies to it. -/
def SingleDefectRouterData.toSaturatingRouterData {P : Type} {E : Type u}
    [Group P] [Group E] {D : BareDefectSourceData P E}
    (R : SingleDefectSaturation.SingleDefectRouterData.{u} D) :
    SaturatingRouterData.{u} D :=
  letI : Group R.Quotient := R.groupQuotient
  letI : Nontrivial R.Quotient := R.nontrivial
  letI : Group.IsFinitelyPresented R.Quotient := R.finitelyPresented
  { Quotient := R.Quotient
    quotient := R.quotient
    kazhdan := R.kazhdan
    torsionFree := R.torsionFree
    generatorOne := R.generatorOne
    generatorTwo := R.generatorTwo
    generates := R.generates
    saturates := R.saturates }

/-! ## 3.  The endpoint over the weakened interface -/

/-- **Output package from a saturating router.**

Identical conclusion to
`BareFullMFRadicalEndpoint.exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_bareRoutingData`,
reached from a strictly weaker hypothesis: the router is no longer asked for a
surjection.

The datum is a genuine hypothesis and this declaration is named
`_of_saturatingRouter` for the same reason the frozen endpoint is named
`_of_bareRoutingData`.  It may not be cited as an unconditional existence
theorem. -/
theorem exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_saturatingRouter
    {P : Type} {E : Type} [Group P] [Group E]
    {D : BareDefectSourceData P E}
    (h : Nonempty (SaturatingRouterData.{0} D)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      cdeMFResidual Q = ⊤ := by
  obtain ⟨R⟩ := h
  letI : Group R.Quotient := R.groupQuotient
  letI : Nontrivial R.Quotient := R.nontrivial
  letI : Group.IsFinitelyPresented R.Quotient := R.finitelyPresented
  exact
    BareFullMFRadicalEndpoint.exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_bareRoutingData
      ⟨R.toBareRoutingData⟩

end PushedDefectSaturation
end GroupApproximation
