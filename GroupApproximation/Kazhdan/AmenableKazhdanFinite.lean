import GroupApproximation.Analysis.PropertyTNonamenable
import GroupApproximation.Manuscript.OneSidedMFRadical.DefectSaturation

/-!
# An amenable group with property `(T)` is finite

`non_mf_groups_exist.tex`, Introduction, the paragraph beginning "If
`ρ : G → GL(V)` is a homomorphism and `V` is finite-dimensional", ends with

> If `G` is amenable, its property-`(T)` subgroup `L` is finite~`\cite{BHV}`;
> then `uLu^{-1}=L`, so `ucu^{-1}` centralizes `L` for every
> `u ∈ Comp_G(L)`, and again `𝔇_G(L)=1`.

The citation is the only literature input in that sentence, and this file
removes it: "amenable and Kazhdan implies finite" is proved here, so the whole
amenable clause becomes a theorem of this development.

## What was already in the repository, and what is new

The analytic content was already proved, in the *contrapositive* form.
`Analysis.PropertyTNonamenable.infinite_kazhdan_not_isAmenable` proves that an
**infinite** group with property `(T)` is not `Amenability.IsAmenable`, by the
classical argument: a Følner set for the symmetrized Kazhdan control set has a
normalized indicator which is an almost invariant unit vector of the left
regular representation on real `ℓ²(G)`, the Kazhdan pair turns it into a
nonzero invariant vector, and an invariant `ℓ²` function is constant on `G`,
hence not square summable when `G` is infinite.  That file states the result
only at `Infinite G`; the manuscript needs the positive form `Finite G`.

The group-theoretic half was also already proved, in
`Manuscript.OneSidedMFRadical.DefectSaturation`: for a **finite** `L`,
`conj_image_eq_of_mem_compressionSet_of_finite` is the printed sentence
`uLu^{-1}=L`, `commute_conj_of_mem_compressionSet_of_finite` is "`ucu^{-1}`
centralizes `L`", and `printedDefect_eq_bot_of_finite` is `𝔇_G(L)=1`.  Those
proofs are *not* repeated here; the theorems below only instantiate them, with
finiteness of `L` now derived rather than cited.

What is new is therefore exactly the missing link and its consequences:
`finite_of_isAmenable_of_kazhdan`, the contrapositive of the nonamenability
theorem stated positively, and the chain down to
`printedDefect_eq_bot_of_isAmenable_of_kazhdan`, which is the manuscript's
amenable clause with no citation attached.

`isAmenable_iff_finite_of_kazhdan` records that for a group with property
`(T)` amenability and finiteness are the *same* condition, the converse being
`Amenability.isAmenable_of_finite`.

## Placement

The module sits under `Kazhdan/` because its subject is property `(T)`, but it
imports `Analysis.PropertyTNonamenable` and the manuscript's defect files.
Both are already in the root import closure, so no cycle is created; nothing
under `Analysis/` or `Manuscript/` imports this file.

Nothing here is conditional: every theorem below is stated without a
hypothesis standing in for an unformalized fact, and
`manuscriptAmenableKazhdanSterility` packages the three conclusions as one
hypothesis-free endpoint.
-/

namespace GroupApproximation

universe u w

/-! ## The theorem -/

section Finiteness

variable {G : Type u} [Group G]

/-- **An amenable group with property `(T)` is finite.**

This is the manuscript's `\cite{BHV}` input, proved rather than cited.  It is
the positive form of `PropertyTNonamenable.infinite_kazhdan_not_isAmenable`,
which rules out the infinite case; the Følner-set argument establishing that
theorem is where all of the analytic content lives. -/
theorem finite_of_isAmenable_of_kazhdan (hT : HasKazhdanPropertyT.{u, u} G)
    (hA : Amenability.IsAmenable G) : Finite G := by
  by_contra hfin
  haveI : Infinite G := not_finite_iff_infinite.mp hfin
  exact PropertyTNonamenable.infinite_kazhdan_not_isAmenable hT hA

/-- The same statement from the textbook complex-unitary form of property
`(T)`, at an arbitrary representation universe. -/
theorem finite_of_isAmenable_of_kazhdanTextbook
    (hT : HasKazhdanPropertyTComplex.{u, max u w} G)
    (hA : Amenability.IsAmenable G) : Finite G := by
  by_contra hfin
  haveI : Infinite G := not_finite_iff_infinite.mp hfin
  exact PropertyTNonamenable.infinite_kazhdanTextbook_not_isAmenable hT hA

/-- **For a group with property `(T)`, amenability and finiteness coincide.**
The forward direction is the theorem above; the converse is that finite groups
carry a normalized counting mean. -/
theorem isAmenable_iff_finite_of_kazhdan (hT : HasKazhdanPropertyT.{u, u} G) :
    Amenability.IsAmenable G ↔ Finite G := by
  refine ⟨fun hA ↦ finite_of_isAmenable_of_kazhdan hT hA, fun hfin ↦ ?_⟩
  haveI := hfin
  exact Amenability.isAmenable_of_finite G

/-- **The manuscript's shape.**  In an amenable ambient group, a subgroup with
property `(T)` is finite: amenability passes to `L`, and `L` is then covered
by the theorem above. -/
theorem finite_subgroup_of_isAmenable_of_kazhdan (hA : Amenability.IsAmenable G)
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{u, u} ↥L) : Finite ↥L :=
  finite_of_isAmenable_of_kazhdan hL (hA.subgroup L)

end Finiteness

/-! ## The manuscript's amenable clause

The three printed sentences that follow "`L` is finite", now with finiteness
supplied by the theorem above instead of by a citation.  Each delegates to the
finite-`L` proof already in `Manuscript.OneSidedMFRadical.DefectSaturation`;
none of that group theory is redone here. -/

section AmenableClause

variable {G : Type u} [Group G]

/-- The printed sentence "`uLu^{-1}=L`", under the printed hypotheses:
one-sided compression of a property-`(T)` subgroup of an amenable group is
already two-sided. -/
theorem conj_image_eq_of_isAmenable_of_kazhdan (hA : Amenability.IsAmenable G)
    {L : Subgroup G} (hL : HasKazhdanPropertyT.{u, u} ↥L) {u : G}
    (hu : u ∈ compressionSet L) :
    (fun x ↦ u * x * u⁻¹) '' (L : Set G) = (L : Set G) := by
  haveI : Finite ↥L := finite_subgroup_of_isAmenable_of_kazhdan hA L hL
  exact Manuscript.OneSidedMFRadical.conj_image_eq_of_mem_compressionSet_of_finite hu

/-- The printed sentence "`ucu^{-1}` centralizes `L`", under the printed
hypotheses. -/
theorem commute_conj_of_isAmenable_of_kazhdan (hA : Amenability.IsAmenable G)
    {L : Subgroup G} (hL : HasKazhdanPropertyT.{u, u} ↥L) {u c : G}
    (hu : u ∈ compressionSet L) (hc : ∀ delta ∈ L, Commute c delta)
    {ell : G} (hell : ell ∈ L) : Commute (u * c * u⁻¹) ell := by
  haveI : Finite ↥L := finite_subgroup_of_isAmenable_of_kazhdan hA L hL
  exact Manuscript.OneSidedMFRadical.commute_conj_of_mem_compressionSet_of_finite
    hu hc hell

/-- **The manuscript's amenable clause, with no citation left in it.**  If the
ambient group is amenable and `L` has property `(T)`, the printed defect
`𝔇_G(L)` is trivial.

This is the third clause of
`Manuscript.OneSidedMFRadical.PrintedDefectSterility`, whose statement there
takes finiteness of `L` as a hypothesis because the passage from amenability
was the cited `BHV` fact.  Here that passage is
`finite_subgroup_of_isAmenable_of_kazhdan`. -/
theorem printedDefect_eq_bot_of_isAmenable_of_kazhdan
    (hA : Amenability.IsAmenable G) (L : Subgroup G)
    (hL : HasKazhdanPropertyT.{u, u} ↥L) :
    Manuscript.OneSidedMFRadical.printedDefect L = ⊥ := by
  haveI : Finite ↥L := finite_subgroup_of_isAmenable_of_kazhdan hA L hL
  exact Manuscript.OneSidedMFRadical.printedDefect_eq_bot_of_finite L

end AmenableClause

/-! ## The closed endpoint -/

/-- The amenable clause of the Introduction's sterility paragraph, packaged as
one proposition: an amenable group with property `(T)` is finite; a
property-`(T)` subgroup of an amenable group is finite; and the printed defect
of such a subgroup is trivial.  No clause carries a hypothesis standing in for
an unformalized theorem. -/
def AmenableKazhdanSterility : Prop :=
  (∀ (G : Type u) [Group G], HasKazhdanPropertyT.{u, u} G →
      Amenability.IsAmenable G → Finite G) ∧
  (∀ (G : Type u) [Group G] (L : Subgroup G), Amenability.IsAmenable G →
      HasKazhdanPropertyT.{u, u} ↥L → Finite ↥L) ∧
  (∀ (G : Type u) [Group G] (L : Subgroup G), Amenability.IsAmenable G →
      HasKazhdanPropertyT.{u, u} ↥L →
        Manuscript.OneSidedMFRadical.printedDefect L = ⊥)

theorem manuscriptAmenableKazhdanSterility : AmenableKazhdanSterility.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ _ hT hA ↦ finite_of_isAmenable_of_kazhdan hT hA
  · exact fun _ _ L hA hL ↦ finite_subgroup_of_isAmenable_of_kazhdan hA L hL
  · exact fun _ _ L hA hL ↦ printedDefect_eq_bot_of_isAmenable_of_kazhdan hA L hL

end GroupApproximation
