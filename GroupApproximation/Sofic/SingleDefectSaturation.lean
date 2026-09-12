import GroupApproximation.Sofic.BareDefectSource

/-!
# Arithmetic single-defect saturation

`BareRoutingData` asks the router for `defect_surjective`: the *whole*
compression defect `⟪[d, ι(P)]⟫` must map onto the routed quotient.  That
is a statement about a distinguished infinitely generated normal subgroup,
and a construction has to preserve all of it.

This file replaces that demand by a strictly weaker one.  Mark a single
element of the defect — the commutator `[d, ι(witness)]` already named by
`BareDefectSourceData.witness`, here called `markedCommutator` — and ask
only that its *image* normally generates the quotient:

  `Subgroup.normalClosure {quotient (markedCommutator D)} = ⊤`.

`defectNormal_map_eq_top_of_saturating_element` is the elementary
observation that this suffices.  The image of a normal subgroup under a
surjection is normal, the marked element lies in the defect, so its image
lies in the image of the defect; a normal subgroup containing a set
contains that set's normal closure, and the closure is everything.  The
lemma is unconditional and is the only mathematical content added here.

## What this is, and what it is not

This is a **new construction route into the existing normal-Kazhdan
analytic engine, not a new analytic mechanism.**  Nothing about MF
algebras, coronas, or Kazhdan pairs is proved or even touched in this
file.  `SingleDefectRouterData.toBareRoutingData` hands the assembled
datum to `BareRoutingData`, and every non-MF consequence — full corona MF
radical, triviality of corona representations, failure of operator-MF for
the quotient and for all of its nontrivial quotients — is the one already
proved there, reached with zero duplication.  The gain is entirely on the
input side: a router now has one element to saturate instead of a
subgroup to preserve.

## The routing datum is consumed, not constructed

`SingleDefectRouterData` is a hypothesis, exactly as `BareRoutingData`
is.  Producing an inhabitant is the acylindrically-hyperbolic
small-cancellation step — a common quotient of the ambient group and a
property-`(T)` partner, finitely presented, torsion-free, two-generated,
in which one prescribed element normally generates.  Mathlib has no
acylindrical hyperbolicity, no rotating families, and no Dehn filling, so
that step is not available to be formalized here and is **not** claimed
below.  No declaration in this file may be cited as an unconditional
existence theorem.

## Two things that do not appear

There is **no simple subgroup and no simplicity-protection argument**.
The `FournierFacioDefectData` route obtained survival of the protected
element from an embedded infinite simple factor; the slimmed route of
`BareDefectSource` deleted the factor but kept `protected_ne_one` as a
postulated field.  Here survival is neither postulated nor imported: it is
**proved**.  `marked_ne_one` derives nontriviality of the routed marked
commutator from `saturates` together with `Nontrivial Quotient` — if the
marked image were trivial its normal closure would be `⊥`, not `⊤` — and
`protected_ne_one` then falls out because a commutator with a trivial left
entry is trivial.  So the single saturation clause pays for both fields
that `BareRoutingData` asks for.

## Relation to the arithmetic source

`GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean` already
supplies the source half of this route, and supplies it unconditionally.
Its `LiteralAffineCongruenceSource.literalBareDefectSourceData` is a closed
`BareDefectSourceData` over the base `P = ℤ³ ⋊ Γ(3)` — the preimage of the
level-three congruence subgroup under the linear part of the literal affine
base — with ambient group the HNN envelope of the translation-doubling
endomorphism, which fixes the linear part, doubles the lattice, and omits
the first translation from its range.  That definition and
`LiteralAffineCongruenceSource.exists_literal_torsionFree_finitelyPresented_bareDefectSource`
are premise-free: neither takes a hypothesis, a routing datum, or a
literature-shaped input.

Those are **consumed facts, recorded here for orientation.  Nothing in this
file re-proves them**, and this module does not import that one.  Read
together with the present file the accounting is exact: the source datum
exists unconditionally, the passage from a routing datum over it to the
full non-MF package is proved, and the one remaining gap between this route
and an unconditional non-MF existence theorem is an inhabitant of
`SingleDefectRouterData` at that datum — the Hull small-cancellation step.
Nothing here claims such an inhabitant exists.
-/

namespace GroupApproximation
namespace SingleDefectSaturation

open scoped commutatorElement

universe u v

/-! ## The marked defect element -/

section MarkedDefect

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)

/-- **The one defect element a single-defect router has to saturate.**

`BareDefectSourceData` already names a base element `witness` whose marked
commutator with the transported root is nontrivial.  This is that
commutator, taken at the transported root `d = u (u⁻¹ s u) u⁻¹` of the
compression core rather than at `s` directly, so that membership in the
compression defect is the literal generating clause
`KazhdanCompressionCore.defect_mem_defectNormal`. -/
def markedCommutator : E :=
  ⁅D.core.transported, D.iota D.witness⁆

/-- The transported root of a slimmed source is the protected element, so
the marked commutator is the source's own marked commutator `[s, ι(p)]`. -/
theorem markedCommutator_eq :
    markedCommutator D = ⁅D.s, D.iota D.witness⁆ := by
  unfold markedCommutator
  rw [D.core_transported]

/-- The marked element is a compression defect: it is literally one of the
generators of `defectNormal`. -/
theorem markedCommutator_mem_defectNormal :
    markedCommutator D ∈ D.core.defectNormal :=
  D.core.defect_mem_defectNormal D.witness

/-- The marked element is nontrivial in the ambient group.  This is the
source's `witness_commutator_ne_one` clause and nothing more. -/
theorem markedCommutator_ne_one : markedCommutator D ≠ 1 := by
  rw [markedCommutator_eq]
  exact D.witness_commutator_ne_one

end MarkedDefect

/-! ## Saturation by one element -/

section Saturation

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)

/-- **One saturating defect element replaces defect surjectivity.**

If some element `w` of the compression defect has an image that normally
generates the target, then the whole compression defect maps onto the
target.

The proof is the two-line one it looks like.  `defectNormal` is normal and
`q` is onto, so `defectNormal.map q` is normal; it contains `q w`; a normal
subgroup containing a set contains the normal closure of that set; and that
closure is `⊤` by hypothesis.

Surjectivity of `q` is used only to know that the image subgroup is normal.
No property of the compression core beyond normality of `defectNormal`
enters, and no property of `w` beyond membership. -/
theorem defectNormal_map_eq_top_of_saturating_element
    {Q : Type v} [Group Q] (q : E →* Q) (hq : Function.Surjective q)
    {w : E} (hw : w ∈ D.core.defectNormal)
    (hsat : Subgroup.normalClosure ({q w} : Set Q) = ⊤) :
    D.core.defectNormal.map q = ⊤ := by
  haveI : (D.core.defectNormal.map q).Normal :=
    Subgroup.Normal.map inferInstance q hq
  apply top_unique
  rw [← hsat]
  exact Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr (Subgroup.mem_map_of_mem q hw))

end Saturation

/-! ## The single-defect routing interface -/

/-- **`BareRoutingData` with defect surjectivity and survival replaced by
one saturation clause.**

Field for field this is `BareRoutingData`, with its last two fields
`defect_surjective` and `protected_ne_one` deleted and replaced by
`quotient_surjective` together with `saturates`.  Both replaced fields are
recovered as theorems in the namespace below, so this interface assumes
strictly less: a router that produces a `SingleDefectRouterData` produces a
`BareRoutingData`, and the converse implication is not claimed.

Surjectivity has to be stored here, unlike in `BareRoutingData`, precisely
because it is no longer derivable from defect surjectivity — it is instead
the hypothesis that makes defect surjectivity derivable.  It is free for any
construction that builds the quotient as a quotient.

This structure is a **hypothesis**, not a theorem.  Producing an inhabitant
is the acylindrically-hyperbolic small-cancellation step described in the
module docstring; nothing in this file constructs one. -/
structure SingleDefectRouterData {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) where
  /-- The routed common quotient. -/
  Quotient : Type
  [groupQuotient : Group Quotient]
  /-- The quotient map from the source. -/
  quotient : E →* Quotient
  /-- The routed quotient is finitely presented. -/
  [finitelyPresented : Group.IsFinitelyPresented Quotient]
  /-- The routed quotient is nontrivial.  Supplied by the router, which
  knows its quotient is not the trivial group; it is what turns the
  saturation clause into survival of the protected element. -/
  [nontrivial : Nontrivial Quotient]
  /-- Property `(T)`, obtained from the Kazhdan partner's surjection. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Quotient
  /-- Hull's torsion-preservation conclusion, in power form. -/
  torsionFree : IsPowerTorsionFree Quotient
  /-- First generator produced by the routing stage. -/
  generatorOne : Quotient
  /-- Second generator produced by the routing stage. -/
  generatorTwo : Quotient
  /-- The two routed elements generate the quotient. -/
  generates :
    Subgroup.closure ({generatorOne, generatorTwo} : Set Quotient) = ⊤
  /-- The routing map is onto.  Free for a construction that builds the
  quotient by imposing relators. -/
  quotient_surjective : Function.Surjective quotient
  /-- **The single-defect clause.**  The image of the one marked defect
  element normally generates the routed quotient.  This is the relator the
  small-cancellation stage imposes, and it replaces both defect
  surjectivity and survival of the protected element. -/
  saturates :
    Subgroup.normalClosure ({quotient (markedCommutator D)} : Set Quotient) = ⊤

namespace SingleDefectRouterData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : BareDefectSourceData P E}
    (R : SingleDefectRouterData.{u} D)

local instance singleDefectQuotientGroup : Group R.Quotient := R.groupQuotient
local instance singleDefectQuotientNontrivial : Nontrivial R.Quotient :=
  R.nontrivial

/-- **Defect surjectivity is derived, not assumed.**  Saturating the one
marked defect element saturates the whole compression defect. -/
theorem defect_surjective : D.core.defectNormal.map R.quotient = ⊤ :=
  defectNormal_map_eq_top_of_saturating_element D R.quotient
    R.quotient_surjective (markedCommutator_mem_defectNormal D) R.saturates

/-- **The routed marked commutator is nontrivial.**  Were it trivial, the
saturation clause would read `⟪1⟫ = ⊤`, and `⟪1⟫` is `⊥`; a nontrivial
quotient forbids `⊥ = ⊤`.

No simplicity and no protected subgroup is used: nontriviality of the routed
quotient plus saturation is the whole argument. -/
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

/-- **The protected element survives, as a theorem.**  A commutator with a
trivial left entry is trivial, so killing `s` would kill the marked
commutator, which `marked_ne_one` forbids.

`BareRoutingData` postulates this as a field and the Fournier--Facio route
obtains it from an embedded simple factor.  Here it is a consequence of the
single saturation clause. -/
theorem protected_ne_one : R.quotient D.s ≠ 1 := by
  intro hs
  apply R.marked_ne_one
  rw [markedCommutator_eq D, map_commutatorElement, hs,
    commutatorElement_one_left]

/-- **The payoff.**  A single-defect routing datum is a `BareRoutingData`,
so the entire full-MF-radical consequence package of `BareDefectSource`
applies verbatim: `coronaMFResidual_eq_top`, `cdeMFResidual_eq_top`,
`not_isOperatorMF`, `quotient_not_isCDEOperatorMF`, and the rest.  Nothing
analytic is redone, and the two fields this interface dropped are supplied
by the two theorems above. -/
def toBareRoutingData : BareRoutingData D where
  Quotient := R.Quotient
  groupQuotient := R.groupQuotient
  quotient := R.quotient
  finitelyPresented := R.finitelyPresented
  kazhdan := R.kazhdan
  torsionFree := R.torsionFree
  generatorOne := R.generatorOne
  generatorTwo := R.generatorTwo
  generates := R.generates
  defect_surjective := R.defect_surjective
  protected_ne_one := R.protected_ne_one

/-! ### End-to-end consequences

Nothing below is new mathematics.  Each statement is the corresponding
`BareRoutingData` theorem of `BareDefectSource`, restated at
`SingleDefectRouterData` and proved by handing over `toBareRoutingData`, so
that what this route delivers is legible without leaving the file.  All of
the analytic content sits in `BareDefectSource` and the normal-Kazhdan
chain beneath it, and none of it is repeated or strengthened here. -/

/-- **Restatement** of `BareRoutingData.normMFResidual_eq_top`: the routed
quotient is its own ultraproduct norm-MF residual — every one of its
elements is invisible in every standard cofinite norm-matrix corona. -/
theorem normMFResidual_eq_top : normMFResidual R.Quotient = ⊤ :=
  R.toBareRoutingData.normMFResidual_eq_top

/-- **Restatement** of `BareRoutingData.not_isOperatorMF`: the routed
quotient is not an MF group.  This is the clause that consumes survival of
the protected element, which `protected_ne_one` above proves rather than
assumes. -/
theorem not_isOperatorMF : ¬ IsOperatorMF R.Quotient :=
  R.toBareRoutingData.not_isOperatorMF

/-- **Restatement** of `BareRoutingData.quotient_not_isOperatorMF`: the
failure is hereditary, so every nontrivial quotient of the routed group
fails to be MF as well. -/
theorem quotient_not_isOperatorMF {H : Type*} [Group H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) : ¬ IsOperatorMF H :=
  R.toBareRoutingData.quotient_not_isOperatorMF q hq

/-- **Restatement** of `BareRoutingData.no_nontrivial_finite_quotient`: the
routed quotient has no nontrivial finite quotient. -/
theorem no_nontrivial_finite_quotient (M : Type) [Group M] [Finite M]
    [Nontrivial M] (f : R.Quotient →* M) : ¬ Function.Surjective f :=
  R.toBareRoutingData.no_nontrivial_finite_quotient M f

/-- **Restatement** of `BareRoutingData.isTwoGenerated`: the two elements
the router produces generate the routed quotient. -/
theorem isTwoGenerated : IsTwoGenerated R.Quotient :=
  R.toBareRoutingData.isTwoGenerated

end SingleDefectRouterData

/-- Any inhabitant of the single-defect routing interface discharges the
slimmed endpoint's single hypothesis.  The hypothesis `h` is supplied, not
proved; this is a transport statement about interfaces. -/
theorem nonempty_bareRoutingData_of_singleDefect
    {P : Type} {E : Type u} [Group P] [Group E]
    {D : BareDefectSourceData P E}
    (h : Nonempty (SingleDefectRouterData.{u} D)) :
    Nonempty (BareRoutingData.{u} D) := by
  obtain ⟨R⟩ := h
  exact ⟨R.toBareRoutingData⟩

end SingleDefectSaturation
end GroupApproximation
