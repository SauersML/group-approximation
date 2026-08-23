import GroupApproximation.Sofic.BareDefectSource
import GroupApproximation.Sofic.HullPrescribedSaturation
import GroupApproximation.Sofic.QuestionTwoReduction

/-!
# The exact bare-defect/Hull endpoint boundary

This file records the concrete output of the two-stage construction in the
form in which Hull's theorem supplies it, and derives the operator-MF endpoint.
It does not assert that the output exists.

Unlike `OrderPreservingRoutingData`, the interface below does not strengthen
Hull's finite-order conclusion to equality of the order of every source
element with the order of its image.  The concrete constructor uses the
published conclusion in its authentic domain: every finite-order element
lifts, with the same order, through the common quotient from the whole free
product and then through the final Hull quotient. Survival of the marked
element is supplied separately by injectivity on the compression factor's
explicitly protected pair `{1, s}`.

The single normal-generation field says that the compression defect maps onto
the quotient. From it Lean derives surjectivity of the ambient quotient map.
Property `(T)` descends from the auxiliary Kazhdan factor in the common-
quotient construction, and the existing compression theorem gives the non-MF
conclusion. No embedded simple factor is part of this interface.
-/

namespace GroupApproximation

universe u

/-! ## The minimal routed output -/

/-- **Concrete output of the bare-defect/Hull construction.**

Every field is a direct construction fact rather than an endpoint conclusion:

* Hull adjoins finitely many relators, so the quotient is finitely presented;
* the target is Kazhdan, derived by `ofCommonQuotientAndHull` from the
  auxiliary factor;
* the target is torsion-free, derived by `ofCommonQuotientAndHull` from
  finite-order lifting along the whole free-product route;
* the compression defect maps onto the quotient;
* each stage is injective on the protected pair or its image.

Target nontriviality, quotient-map surjectivity, saturation of the descended
compression core, and non-MF are not fields. The abstract boundary stores the
two target properties actually consumed by the endpoint.  The authentic
`ofCommonQuotientAndHull` constructor derives them from the auxiliary Kazhdan
factor and the torsion-free free-product source rather than assuming them as
independent target facts. -/
structure BareDefectHullQuotientData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) where
  /-- The quotient constructed by the small-cancellation step. -/
  Quotient : Type
  [groupQuotient : Group Quotient]
  /-- The quotient map from the compression ambient group. -/
  quotient : E →* Quotient
  /-- Only finitely many relators are adjoined. -/
  [finitelyPresented : Group.IsFinitelyPresented Quotient]
  /-- Torsion-freeness of the final target, derived by the concrete constructor
  from the whole free-product source and the two finite-order lifting stages. -/
  targetTorsionFree : IsPowerTorsionFree Quotient
  /-- Property `(T)` of the target. In `ofCommonQuotientAndHull` this is
  derived from the auxiliary Kazhdan factor and its surjection, not from the
  ambient group. -/
  targetKazhdan : HasKazhdanPropertyT.{0, 0} Quotient
  /-- Hull's direct saturation conclusion for the compression defect. -/
  defectNormal_maps_top : D.core.defectNormal.map quotient = ⊤
  /-- Injectivity on the deliberately protected pair `{1, s}`. -/
  protected_injective : Set.InjOn quotient ({1, D.s} : Set E)

namespace BareDefectHullQuotientData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : BareDefectSourceData P E}
    (H : BareDefectHullQuotientData D)

local instance hullQuotientGroup : Group H.Quotient := H.groupQuotient
local instance hullQuotientFinitelyPresented :
    Group.IsFinitelyPresented H.Quotient := H.finitelyPresented

/-! ## Direct input from the common quotient and Hull saturation -/

/-- Build the endpoint datum directly from the authentic common-quotient maps
and the subsequent Hull quotient.

The auxiliary-factor map `first : A → M` is onto.  The map `source : F → M`
comes from the whole torsion-free free product used in the common quotient;
its finite-order lifting clause, followed by the corresponding clause for
`finish`, proves that `Q` is torsion-free.  This route deliberately does not
try to lift torsion through `second : E → M`: the compression source `E` is
only one factor of `F`.

No separate surjectivity
assumption on `second : E → M` is needed at this endpoint: Hull's direct
saturation conclusion already says that the image under `finish` of the
mapped compression defect is all of `Q`, and therefore implies
surjectivity of the final source composite. `Subgroup.map_map` turns that
statement into saturation under the composite map from `E`. Property `(T)`
descends along the surjective composite from the auxiliary Kazhdan factor
`A`. Protected-set injectivity is supplied one Hull stage at a time and
composed here. -/
def ofCommonQuotientAndHull
    {A : Type} {F M : Type*} {Q : Type}
    [Group A] [Group F] [Group M] [hQ : Group Q]
    [hQfp : Group.IsFinitelyPresented Q]
    (first : A →* M) (source : F →* M) (second : E →* M)
    (finish : M →* Q)
    (hfirst : Function.Surjective first)
    (hFtor : IsPowerTorsionFree F)
    (hAT : HasKazhdanPropertyT.{0, 0} A)
    (hsaturation : (D.core.defectNormal.map second).map finish = ⊤)
    (horderSource : ∀ (y : M) (n : ℕ), 0 < n → orderOf y = n →
      ∃ x : F, orderOf x = n ∧ source x = y)
    (horderFinish : ∀ (z : Q) (n : ℕ), 0 < n → orderOf z = n →
      ∃ y : M, orderOf y = n ∧ finish y = z)
    (hprotectedSecond : Set.InjOn second ({1, D.s} : Set E))
    (hprotectedFinish :
      Set.InjOn finish (second '' ({1, D.s} : Set E))) :
    BareDefectHullQuotientData D := by
  have hfinish : Function.Surjective finish := by
    intro y
    have hy : y ∈ (D.core.defectNormal.map second).map finish := by
      rw [hsaturation]
      exact Subgroup.mem_top y
    obtain ⟨m, -, hm⟩ := Subgroup.mem_map.mp hy
    exact ⟨m, hm⟩
  have hfirstFinal : Function.Surjective (finish.comp first) :=
    hfinish.comp hfirst
  exact {
    Quotient := Q
    groupQuotient := hQ
    quotient := finish.comp second
    finitelyPresented := hQfp
    targetTorsionFree :=
      isPowerTorsionFree_of_orderReflecting hFtor (finish.comp source)
        (HullPrescribedSaturation.finiteOrder_lifts_comp source finish
          horderSource horderFinish)
    targetKazhdan :=
      HasKazhdanPropertyT.of_surjective (finish.comp first) hfirstFinal hAT
    defectNormal_maps_top := by
      rw [← Subgroup.map_map]
      exact hsaturation
    protected_injective :=
      HullPrescribedSaturation.injOn_comp second finish ({1, D.s} : Set E)
        hprotectedSecond hprotectedFinish }

/-! ## Direct consumption of the bespoke router -/

/-- The bespoke small-cancellation router already has exactly the concrete
fields stored by `BareDefectHullQuotientData`.  This adapter makes that fact
literal: torsion-freeness and finite presentation are carried by the router,
property `(T)` descends from its surjective partner map, saturation is its
`defect_top` conclusion, and protected-pair injectivity is unchanged.

Unlike `ofCommonQuotientAndHull`, this constructor consumes the collapsed
one-stage output after both quotient steps have been assembled.  It introduces
no existence assumption and no endpoint property as a separate hypothesis. -/
def _root_.GroupApproximation.SmallCancellationRouter.RoutingLemmaData.toBareDefectHullQuotientData
    {B : Type} [Group B]
    (R : SmallCancellationRouter.RoutingLemmaData
      E D.core.defectNormal D.s B)
    (hB : HasKazhdanPropertyT.{0, 0} B) :
    BareDefectHullQuotientData D where
  Quotient := R.Quotient
  groupQuotient := R.groupQuotient
  quotient := R.route
  finitelyPresented := R.finitelyPresented
  targetTorsionFree := R.torsionFree
  targetKazhdan := R.kazhdan hB
  defectNormal_maps_top := R.defect_top
  protected_injective := R.protected_injOn

/-- Existential form of
`RoutingLemmaData.toBareDefectHullQuotientData`.  Thus an actual router at a
bare source is now the sole construction datum needed by the torsion-free
non-MF endpoint. -/
theorem nonempty_of_routingLemmaData
    {B : Type} [Group B]
    (hB : HasKazhdanPropertyT.{0, 0} B)
    (hR : Nonempty (SmallCancellationRouter.RoutingLemmaData
      E D.core.defectNormal D.s B)) :
    Nonempty (BareDefectHullQuotientData D) := by
  obtain ⟨R⟩ := hR
  exact ⟨R.toBareDefectHullQuotientData hB⟩

/-- The ambient map is onto; this is derived from normal generation rather
than stored as a second version of the same Hull conclusion. -/
theorem quotient_surjective : Function.Surjective H.quotient :=
  fun y ↦ by
    have hy : y ∈ D.core.defectNormal.map H.quotient := by
      rw [H.defectNormal_maps_top]
      exact Subgroup.mem_top y
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, hx⟩

/-- Property `(T)` of the target, whose two-stage constructor derives it from
the auxiliary Kazhdan factor. -/
theorem quotient_kazhdan : HasKazhdanPropertyT.{0, 0} H.Quotient :=
  H.targetKazhdan

/-- Torsion-freeness of the target, derived by the concrete constructor from
the whole torsion-free free-product source. -/
theorem quotient_torsionFree : IsPowerTorsionFree H.Quotient :=
  H.targetTorsionFree

/-- The protected element survives. This is deliberately derived from the
geometric injectivity conclusion and is not an existence-sounding field. -/
theorem protected_ne_one : H.quotient D.s ≠ 1 := by
  intro hs
  apply D.s_ne_one
  apply H.protected_injective (Set.mem_insert_of_mem _ rfl)
    (Set.mem_insert _ _)
  simpa using hs

/-- A finitely presented quotient is countable. -/
theorem quotientCountable : Countable H.Quotient := by
  obtain ⟨n, f, hsurj, -⟩ := H.finitelyPresented.out
  letI : Countable (FreeGroup (Fin n)) := by
    have hfree : Function.Surjective
        (FreeGroup.mk : List (Fin n × Bool) → FreeGroup (Fin n)) := by
      intro g
      obtain ⟨L, hL⟩ := Quot.exists_rep g
      exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
    exact hfree.countable
  exact hsurj.countable

local instance hullQuotientCountable : Countable H.Quotient :=
  H.quotientCountable

/-- The quotient is nontrivial because the protected element survives. -/
theorem quotientNontrivial : Nontrivial H.Quotient :=
  ⟨⟨H.quotient D.s, 1, H.protected_ne_one⟩⟩

/-- Hull's direct saturation conclusion, exposed under a theorem name for the
mapped-core argument below. -/
theorem defectNormal_map_eq_top :
    D.core.defectNormal.map H.quotient = ⊤ :=
  H.defectNormal_maps_top

/-- After descent to the quotient, the compression defect is the whole
quotient. -/
theorem mapped_defectNormal_eq_top :
    (D.core.map H.quotient).defectNormal = ⊤ := by
  apply top_unique
  rw [← H.defectNormal_map_eq_top]
  exact D.core.map_subgroup_le_defectNormal H.quotient
    D.core.defectNormal le_rfl

/-- The verified normal-Kazhdan compression theorem applied at `K = ⊤`. -/
theorem not_isOperatorMF : ¬ IsOperatorMF H.Quotient := by
  letI : Countable H.Quotient := H.quotientCountable
  letI : Nontrivial H.Quotient := H.quotientNontrivial
  have hTtop : HasKazhdanPropertyT.{0, 0} (⊤ : Subgroup H.Quotient) :=
    HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv H.quotient_kazhdan
  exact QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect
    (D.core.map H.quotient) ⊤ hTtop (by rw [H.mapped_defectNormal_eq_top])
      top_ne_bot

/-- Literal Carrión--Dadarlat--Eckhardt formulation. -/
theorem not_isCDEOperatorMF : ¬ IsCDEOperatorMF H.Quotient := by
  rw [isCDEOperatorMF_iff_isOperatorMF]
  exact H.not_isOperatorMF

include H in
/-- The exact existential endpoint obtained from one concrete two-stage
output. There is no additional routing, Kazhdan, torsion-free, survival, or
non-MF assumption: each is a theorem of `H`. -/
theorem to_exists_torsionFree_finitelyPresented_not_MF :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsPowerTorsionFree Q ∧
      Group.IsFinitelyPresented Q ∧
      ¬ IsCDEOperatorMF Q ∧
      ¬ IsOperatorMF Q := by
  letI : Countable H.Quotient := H.quotientCountable
  exact ⟨H.Quotient, inferInstance, inferInstance, H.quotient_torsionFree,
    H.finitelyPresented, H.not_isCDEOperatorMF, H.not_isOperatorMF⟩

end BareDefectHullQuotientData

namespace SmallCancellationRouter

/-- An actual bespoke-router output over a bare compression source gives the
exact torsion-free finitely presented non-MF existential.  All endpoint
properties are derived: the only construction input is the router itself, and
property `(T)` is transported from its certified partner. -/
theorem exists_torsionFree_finitelyPresented_not_MF_of_routingLemmaData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)
    {B : Type} [Group B]
    (hB : HasKazhdanPropertyT.{0, 0} B)
    (hR : Nonempty (RoutingLemmaData E D.core.defectNormal D.s B)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsPowerTorsionFree Q ∧
      Group.IsFinitelyPresented Q ∧
      ¬ IsCDEOperatorMF Q ∧
      ¬ IsOperatorMF Q := by
  obtain ⟨H⟩ :=
    BareDefectHullQuotientData.nonempty_of_routingLemmaData (D := D) hB hR
  exact BareDefectHullQuotientData.to_exists_torsionFree_finitelyPresented_not_MF H

end SmallCancellationRouter

end GroupApproximation
