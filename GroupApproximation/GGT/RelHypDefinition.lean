import GroupApproximation.GGT.RelHypRelativeCayley
import GroupApproximation.GGT.WPDHyperbolicallyEmbedded
import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Algebra.CoprodIFinitePresentation
import GroupApproximation.Kazhdan.AmenableKazhdanFinite
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Labelled relative hyperbolicity, the free product `U ∗ H`, and non-elementarity

Three things the Fournier-Facio input paragraph needs before Osin's small
cancellation theorem can be quoted at all.

## 1.  Relative hyperbolicity

`IsRelativelyHyperbolic G H` is the labelled DGO notion: there is a finite
relative base `X` for which the family `H` is hyperbolically embedded in
`(G,X)`.  The relative alphabet is the disjoint union of base letters and
indexed peripheral letters (`RelLetter`), and `d̂_λ` forbids precisely
`λ`-labelled edges starting in `H_λ`.  Thus equal subgroups with different
indices remain different edge families.

This is the characterisation of Osin relative hyperbolicity in
Dahmani--Guirardel--Osin, arXiv:1111.7048, Proposition 4.28, compared with
Osin, *Relatively hyperbolic groups*, Memoirs AMS 179 (2006).  The former
endpoint-only definition remains below solely as the legacy
`RelativeGeneratingSet`/`PeripheralMetricLocallyFinite` vocabulary.  It is
not used in `IsRelativelyHyperbolic`: `RelHypOsin24Glue` records the duplicate-
peripheral countermodel showing that endpoint avoidance forgets labels and is
strictly stronger than DGO's relative metric.

## 2.  The free product, and its peripheral factor

`pairFamily U H` is the two-factor family indexed by `Bool`, index `false` the
peripheral factor `U` and index `true` the hyperbolic factor `H`; `Bool` is
used, rather than `Fin 2`, because a match on it reduces definitionally with no
numeral coercion in the way, and because
`Sofic/OsinRelativeSmallCancellation.lean` -- the module this development
feeds -- works over an arbitrary index type with `CoprodI` and never over the
binary `Monoid.Coprod`.  `Algebra/FreeProductOrder.lean` records a *measured*
elaboration blowup for the bridge between the two, so the bridge is not
crossed.

`FreeProductRelativelyHyperbolicStatement` is the one geometric fact the
Fournier-Facio argument imports and this development does not prove:

> if `H` is word hyperbolic then `U ∗ H` is hyperbolic relative to the factor
> `U`, for every group `U`.

It is a theorem of Osin (Memoirs, Theorem 2.34: a group hyperbolic relative to
`{H_λ}` stays so after a free product with a hyperbolic group, the new factor
being absorbed into the ambient geometry) and of Bowditch; the proof is the
Bass--Serre tree of the free product, whose vertex spaces are copies of
`Γ(H, X)` and coned peripheral cosets glued along single points.  Stated here
as a named `Prop` so that every consumer carries it visibly.

## 3.  Non-elementarity, which is where property `(T)` earns its place

Osin's theorem requires the ambient group to be non-elementary.  In the
manuscript's application the peripheral factor is `U` and the ambient geometry
comes from `H`, which must be a **non-elementary** hyperbolic group -- an
infinite hyperbolic group that is not virtually cyclic.  Infinitude alone does
not give this: `ℤ` is infinite, finitely presented, torsion-free and
hyperbolic, and is elementary.

`not_isElementaryGroup_of_infinite_of_kazhdan` is the derivation the manuscript
relies on and this module proves: an infinite group with property `(T)` is not
elementary, because an elementary group is amenable and an amenable group with
property `(T)` is finite -- and *that* step is already a theorem of this
repository (`finite_of_isAmenable_of_kazhdan`, Kazhdan/AmenableKazhdanFinite),
not a citation.  The one input is `ElementaryAmenableStatement`, that a
virtually cyclic group is amenable; it is standard (amenability is closed under
extensions and passes from a finite-index subgroup to the whole group) and is
named rather than proved because this repository's `Amenability.IsAmenable` is
an invariant-mean definition with no finite-index permanence lemma yet.

`GGT/RelHypWithoutKazhdan.lean` proves, unconditionally, that the
property-`(T)` hypothesis cannot simply be deleted from the manuscript's
statement: at `H₀ = ℤ` -- infinite, finitely presented, torsion-free,
hyperbolic, and elementary -- every quotient is commutative, so `F₂` embeds in
none of them.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## 1.  Relative hyperbolicity -/

/-- **Farb's weak relative hyperbolicity**, using the same labelled relative
generating object as the full definition but retaining only its hyperbolicity
clause. -/
def IsWeaklyRelativelyHyperbolic (G : Type u) [Group G] {ι : Type v}
    (H : ι → Subgroup G) : Prop :=
  ∃ D : GGT.RelGenSet G ι, D.base.Finite ∧ D.fam = H ∧
    ∃ delta : ℝ, HullGeometry.IsHyperbolicSpace delta (Cayley D.alphabet)

/-- **The second clause**: the metric induced on a peripheral subgroup by paths
avoiding it is locally finite.

`h` ranges over `H l` and the set is the `n`-ball of `d̂_l` about the identity.
The ball is written as "some avoiding path of length at most `n` exists" rather
than as a `wordNorm` bound, because `d̂_l` takes the value `∞` -- there need be
no avoiding path at all -- and an infimum over an empty set of lengths would
put every unreachable element in every ball. -/
def PeripheralMetricLocallyFinite {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} (X : RelativeGeneratingSet G H) : Prop :=
  ∀ (l : ι) (n : ℕ),
    {h : G | h ∈ H l ∧ ∃ m ∈ X.peripheralLengths l h, m ≤ n}.Finite

/-- Forget only the obsolete endpoint-path encoding, retaining the same finite
base and family as a labelled `RelGenSet`.  The alphabets have the same vertex
metric; the new object additionally distinguishes peripheral edge labels. -/
def RelativeGeneratingSet.toRelGenSet {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} (X : RelativeGeneratingSet G H) :
    GGT.RelGenSet G ι where
  base := X.carrier
  fam := H
  symmetricGenerating := X.alphabet.symmetricGenerating

@[simp] theorem RelativeGeneratingSet.toRelGenSet_base
    {G : Type u} [Group G] {ι : Type v} {H : ι → Subgroup G}
    (X : RelativeGeneratingSet G H) : X.toRelGenSet.base = X.carrier := rfl

@[simp] theorem RelativeGeneratingSet.toRelGenSet_fam
    {G : Type u} [Group G] {ι : Type v} {H : ι → Subgroup G}
    (X : RelativeGeneratingSet G H) : X.toRelGenSet.fam = H := rfl

/-- **A relatively hyperbolic pair (labelled DGO/Osin form).**

This is DGO Proposition 4.28 as a definitional bridge: Osin relative
hyperbolicity is a finite relative base together with a hyperbolically embedded
peripheral family.  `RelGenSet` spells paths in `X ⊔ ⨆ H_λ`, so its relative
balls retain the peripheral index carried by every edge. -/
def IsRelativelyHyperbolic (G : Type u) [Group G] {ι : Type v}
    (H : ι → Subgroup G) : Prop :=
  ∃ D : GGT.RelGenSet G ι,
    D.base.Finite ∧ D.fam = H ∧ D.IsHyperbolicallyEmbedded

theorem IsRelativelyHyperbolic.weak {G : Type u} [Group G] {ι : Type v}
    {H : ι → Subgroup G} (h : IsRelativelyHyperbolic G H) :
    IsWeaklyRelativelyHyperbolic G H := by
  obtain ⟨D, hfinite, hfam, hemb⟩ := h
  exact ⟨D, hfinite, hfam, hemb.hyperbolic⟩

/-- Constructor form used by quotient-preservation and free-product bridges. -/
theorem isRelativelyHyperbolic_of_relGenSet {G : Type u} [Group G]
    {ι : Type v} {H : ι → Subgroup G} (D : GGT.RelGenSet G ι)
    (hfinite : D.base.Finite) (hfam : D.fam = H)
    (hemb : D.IsHyperbolicallyEmbedded) : IsRelativelyHyperbolic G H :=
  ⟨D, hfinite, hfam, hemb⟩

/-! ## 2.  The free product `U ∗ H` and its peripheral factor -/

/-- The two-factor family: index `false` is the peripheral factor `U`, index
`true` the hyperbolic factor `H`. -/
def pairFamily (U H : Type) : Bool → Type
  | false => U
  | true => H

instance instPairFamilyGroup (U H : Type) [Group U] [Group H] :
    ∀ b, Group (pairFamily U H b)
  | false => inferInstanceAs (Group U)
  | true => inferInstanceAs (Group H)

instance instPairFamilyFinitelyPresented (U H : Type) [Group U] [Group H]
    [Group.IsFinitelyPresented U] [Group.IsFinitelyPresented H] :
    ∀ b, Group.IsFinitelyPresented (pairFamily U H b)
  | false => inferInstanceAs (Group.IsFinitelyPresented U)
  | true => inferInstanceAs (Group.IsFinitelyPresented H)

/-- Decidable equality on the two factors, chosen classically.  Supplied as a
`def` and **not** as an instance, for the reason
`Sofic/RelativeRouterEnvelope.lean` records at its own copy: registering a
classical `DecidableEq` for an arbitrary group would derail instance search
everywhere else.  A caller writes `haveI := pairFamilyDecEq U H`. -/
noncomputable def pairFamilyDecEq (U H : Type) :
    ∀ b, DecidableEq (pairFamily U H b) :=
  fun _ => Classical.decEq _

/-- Torsion-freeness of the two factors, as one family. -/
theorem isPowerTorsionFree_pairFamily {U H : Type} [Group U] [Group H]
    (hU : IsPowerTorsionFree U) (hH : IsPowerTorsionFree H) :
    ∀ b, IsPowerTorsionFree (pairFamily U H b)
  | false => hU
  | true => hH

/-- **The peripheral subgroup of `U ∗ H`**: the image of the factor `U`.  It is
isomorphic to `U` by `Monoid.CoprodI.of_injective`. -/
def freeProductPeripheral (U H : Type) [Group U] [Group H] :
    Subgroup (Monoid.CoprodI (pairFamily U H)) :=
  MonoidHom.range
    (Monoid.CoprodI.of :
      pairFamily U H false →* Monoid.CoprodI (pairFamily U H))

/-- **The map `U → (U ∗ H)/K`.**  Written with source `U` rather than
`pairFamily U H false`, so that every statement about it is a statement about
subgroups of `U`; it is the same map as
`OsinSmallCancellation.factorMap K false`. -/
def leftFactorHom {U H : Type} [Group U] [Group H]
    (K : Subgroup (Monoid.CoprodI (pairFamily U H))) [K.Normal] :
    U →* Monoid.CoprodI (pairFamily U H) ⧸ K :=
  (QuotientGroup.mk' K).comp
    (Monoid.CoprodI.of :
      pairFamily U H false →* Monoid.CoprodI (pairFamily U H))

/-- **The map `H → (U ∗ H)/K`**, the same for the hyperbolic factor. -/
def rightFactorHom {U H : Type} [Group U] [Group H]
    (K : Subgroup (Monoid.CoprodI (pairFamily U H))) [K.Normal] :
    H →* Monoid.CoprodI (pairFamily U H) ⧸ K :=
  (QuotientGroup.mk' K).comp
    (Monoid.CoprodI.of :
      pairFamily U H true →* Monoid.CoprodI (pairFamily U H))

/-- **The geometric input of Fournier-Facio, Proposition 2.3**: a free product
with a hyperbolic group is hyperbolic relative to the other factor.

Osin, Memoirs 179 (2006), Theorem 2.34; Bowditch, *Relatively hyperbolic
groups*, §9.  The proof is the Bass--Serre tree of the free product: coning off
the cosets of `U` collapses the `U`-vertex spaces to points, leaving a tree of
copies of `Γ(H, X)` glued along single points, which is hyperbolic because `H`
is.  Not proved here. -/
def FreeProductRelativelyHyperbolicStatement : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H),
    Hyperbolic.IsHyperbolicGroup H →
      IsRelativelyHyperbolic (Monoid.CoprodI (pairFamily U H))
        (fun _ : Unit => freeProductPeripheral U H)

/-! ## 3.  Elementary and non-elementary groups -/

/-- **An elementary group**: one with a cyclic subgroup of finite index.  For a
hyperbolic group this is the standard meaning of "elementary" -- finite, or
virtually `ℤ` -- and it is exactly the class Osin's theorem must exclude. -/
def IsElementaryGroup (G : Type u) [Group G] : Prop :=
  ∃ C : Subgroup G, C.FiniteIndex ∧ IsCyclic ↥C

/-- **A non-elementary hyperbolic group.** -/
def IsNonElementaryHyperbolic (G : Type u) [Group G] : Prop :=
  Hyperbolic.IsHyperbolicGroup G ∧ ¬ IsElementaryGroup G

/-- **Virtually cyclic groups are amenable.**  Standard: a cyclic group is
amenable, and amenability passes from a finite-index subgroup to the whole
group.  Named rather than proved because `Algebra/Amenable.lean` defines
amenability by an invariant mean and carries no finite-index permanence
lemma. -/
def ElementaryAmenableStatement : Prop :=
  ∀ (G : Type) (_ : Group G), IsElementaryGroup G → Amenability.IsAmenable G

/-- **An infinite group with property `(T)` is not elementary.**

This is the step that lets the manuscript's `H₀` -- infinite, hyperbolic, with
property `(T)` -- be fed to Osin's theorem, which needs non-elementarity.  The
analytic half is already a theorem of this repository: an amenable group with
property `(T)` is finite. -/
theorem not_isElementaryGroup_of_infinite_of_kazhdan
    (hEA : ElementaryAmenableStatement) {G : Type} [Group G] [Infinite G]
    (hT : HasKazhdanPropertyT.{0, 0} G) : ¬ IsElementaryGroup G := by
  intro hel
  have hA : Amenability.IsAmenable G := hEA G inferInstance hel
  haveI : Finite G := finite_of_isAmenable_of_kazhdan hT hA
  exact not_finite G

/-- **The manuscript's `H₀` is a non-elementary hyperbolic group.**  Infinite,
hyperbolic and Kazhdan is enough; without property `(T)` it is not, and
`GGT/RelHypWithoutKazhdan.lean` exhibits `ℤ` as the counterexample. -/
theorem isNonElementaryHyperbolic_of_kazhdan
    (hEA : ElementaryAmenableStatement) {G : Type} [Group G] [Infinite G]
    (hhyp : Hyperbolic.IsHyperbolicGroup G) (hT : HasKazhdanPropertyT.{0, 0} G) :
    IsNonElementaryHyperbolic G :=
  ⟨hhyp, not_isElementaryGroup_of_infinite_of_kazhdan hEA hT⟩

end RelHyp
end GGT
end GroupApproximation
