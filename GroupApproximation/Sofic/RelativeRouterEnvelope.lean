import GroupApproximation.Sofic.GreendlingerRelativeTransfer
import GroupApproximation.Sofic.FreeProductRouterObstruction
import GroupApproximation.Sofic.FournierFacioUniversalGroup
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner

/-!
# The relative router: a Kazhdan envelope from a free-product small-cancellation
design, and the exact reason its property-`(T)` clause cannot be designed

`FournierFacioUniversal.KazhdanEnvelope U` asks for four things: a finitely
presented, torsion-free, property-`(T)` group with an injective homomorphism
from `U`.  The literature route is Osin's small cancellation over the
relatively hyperbolic pair `(U * H, U)`, and it is a typed input.  This module
runs the repository's own router pattern *relatively* instead — over the free
product `U * B` with `B` the certified torsion-free finitely presented Kazhdan
partner `CongruenceSubgroup.gamma3Partner` (`Γ(3)`, every field proved) — and
reports exactly how far that gets.

## What the design delivers, and what it cannot

Three of the four clauses come out of the design with no new mathematics beyond
the two open leaves of `Sofic.GreendlingerRelativeTransfer`:

* **finite presentation** — `RelativeRouterDesign.finitelyPresented`, and it
  spends no leaf at all: a free product of two finitely presented groups is
  finitely presented
  (`FreeProductRouterObstruction.isFinitelyPresented_coprodI_bool`) and the
  family is finite;
* **torsion-freeness** — `RelativeRouterDesign.torsionFree`, from
  `GreendlingerRelativeTransfer.osin_conclusion_of_metric`: the torsion of the
  quotient conjugates into the factors, and both factors are torsion-free (`U`
  by hypothesis, `B` by `CongruenceSubgroup.gamma3_torsionFree`);
* **`U` embeds** — `RelativeRouterDesign.emb_injective`, the free-product
  Greendlinger factor-embedding clause
  (`OsinSmallCancellation.factorMap_injective_of_cyclicallyReduced`), applied at
  the source index.

The fourth clause, property `(T)`, is an **explicit hypothesis** of
`kazhdanEnvelope_of_design`, and section 5 proves that this is not squeamishness:
*within the whole-syllable free-product framework the clause cannot be supplied
by tie relators at all.*

## Section 5, in one line: the tie route is refuted, not merely unproved

The briefing this module was written from proposed the standard trick — make the
partner's image fill the quotient, so that `(T)` descends along
`HasKazhdanPropertyT.of_surjective` exactly as `RoutingLemmaData.kazhdan` does —
while keeping `U` embedded by the factor-embedding clause.  Both halves are
individually available here.  Together they are **inconsistent with the design's
own length floor**, and the reason is a single arithmetic fact about the
syllable metric:

> In `U * B` every element of the partner factor is **one syllable**.  So a
> relation making a source generator equal to a partner element is a relator
> subgroup member of syllable length at most `2`
> (`FreeProductCyclic.sylLength_mul_le`), whereas
> `GreendlingerRelativeTransfer.FragmentSlack` forces every relator to have at
> least `42` syllables, and `GreendlingerLengthBound` then demands a relator
> shorter than `2 · 2`.

That is `not_greendlingerLengthBound_of_tie`, and it is unconditional.  Three
consequences are recorded, in increasing strength:

* `RelativeRouterDesign.exists_tie_of_partnerSurjective` — a surjective partner
  map *is* a tie, at every source element;
* `RelativeRouterDesign.exists_injective_to_partner` — if the partner map is
  onto then, the length bound being what it is, the partner map is bijective
  (`FreeProductRouterObstruction.factorMap_bijective_of_surjective`) and `U`
  embeds in `B` itself; with `FournierFacioUniversal.universal_comp` this makes
  `Γ(3)` universal for finitely presented torsion-free groups, which it is not —
  `Γ(3)` is a subgroup of `SL₃(ℤ)`, hence residually finite, while Higman's group
  is finitely presented, torsion-free and has no nontrivial finite quotient at
  all;
* `RelativeRouterDesign.not_partnerSurjective` — the outright refutation: given
  the length bound and one nonidentity element of the source, the partner map is
  never onto.

So this is the free lane's obstruction (`Sofic.FreeProductRouterObstruction`,
which shows a factor that surjects *is* the quotient) transported to the
envelope, with the extra numerical sharpening that the collision is already
visible at the level of relator lengths and needs no bijection argument.

## What would supply the missing clause

Not a better relator family: the obstruction is in the *metric*.  Osin's
relative small cancellation measures pieces in the alphabet `X ∪ U`, where `X`
is a finite generating set of the hyperbolic partner, so a partner element has
the length of its `X`-word and a tie relator `u · w⁻¹` is as long as `w`.  The
in-repo `OsinSmallCancellation.wlen` gives every partner element length one,
which is exactly the collapse above.  The missing engine is therefore a
*weighted* syllable length in which the partner factor carries its own word
metric — a refinement of the definitions in
`Sofic.OsinRelativeSmallCancellation`, not of anything proved there or here.
Section 5 is written so that a future weighted lane can reuse everything above
it unchanged: nothing in sections 1--4 mentions a tie.

## Nothing here is a typed literature input

Every open statement is a named hypothesis in a binder list.  The two that are
genuinely open are `GreendlingerRelativeTransfer.RelativeGreendlingerLeaf` and
`GreendlingerRelativeTransfer.RelativeTorsionLeaf`, at the constant `1/7`; they
are the relative-transfer module's own leaves, spent here once each and always
visibly.  The property-`(T)` clause is a third named hypothesis, and section 5
says precisely why it has to be one.
-/

namespace GroupApproximation
namespace RelativeRouterEnvelope

open Monoid Monoid.CoprodI OsinSmallCancellation GreendlingerRelativeTransfer
open FournierFacioUniversal

/-! ## 0.  The two-factor family, and its retraction onto the source

The ambient group is the indexed free product over `Bool`: index `false` is the
source factor, index `true` the partner factor.  `Bool` is used rather than
`Fin 2` because a match on it reduces definitionally with no numeral coercion in
the way, and because `Sofic.FreeProductRouterObstruction` already works at that
index type. -/

section Family

/-- The two-factor family `U * B`: index `false` is the source, index `true` is
the partner. -/
def factors (U B : Type) : Bool → Type
  | false => U
  | true => B

instance instFactorsGroup (U B : Type) [Group U] [Group B] :
    ∀ b, Group (factors U B b)
  | false => inferInstanceAs (Group U)
  | true => inferInstanceAs (Group B)

instance instFactorsFinitelyPresented (U B : Type) [Group U] [Group B]
    [Group.IsFinitelyPresented U] [Group.IsFinitelyPresented B] :
    ∀ b, Group.IsFinitelyPresented (factors U B b)
  | false => inferInstanceAs (Group.IsFinitelyPresented U)
  | true => inferInstanceAs (Group.IsFinitelyPresented B)

/-- The decidable-equality data the syllable machinery consumes, chosen
classically.  Supplied as a `def` and **not** as an instance on purpose:
registering a classical `DecidableEq` for an arbitrary group would derail
instance search everywhere else in the library.  A caller writes
`letI := classicalFactorsDecEq U B` at the point of use. -/
noncomputable def classicalFactorsDecEq (U B : Type) :
    ∀ b, DecidableEq (factors U B b) :=
  fun _ => Classical.decEq _

end Family

section Retraction

/-- The factorwise data of the retraction onto the source factor: the identity
on the source, the trivial map on the partner. -/
def sourceRetractionFactor (G : Bool → Type) [∀ b, Group (G b)] :
    ∀ b, G b →* G false
  | false => MonoidHom.id (G false)
  | true => 1

/-- **The retraction of the free product onto its source factor.**  It exists
because a free product has the universal property, and it is the only thing
needed to see that a source syllable and a partner syllable never cancel. -/
def sourceRetraction (G : Bool → Type) [∀ b, Group (G b)] : CoprodI G →* G false :=
  CoprodI.lift (sourceRetractionFactor G)

theorem sourceRetraction_of_source (G : Bool → Type) [∀ b, Group (G b)]
    (x : G false) : sourceRetraction G (CoprodI.of x) = x :=
  CoprodI.lift_of (sourceRetractionFactor G) x

theorem sourceRetraction_of_partner (G : Bool → Type) [∀ b, Group (G b)]
    (x : G true) : sourceRetraction G (CoprodI.of x) = 1 :=
  CoprodI.lift_of (sourceRetractionFactor G) x

/-- **A source syllable is never a partner syllable**, unless it is trivial.
The retraction sees the source letter and forgets the partner one. -/
theorem tieWord_ne_one {G : Bool → Type} [∀ b, Group (G b)] {x : G false}
    (hx : x ≠ 1) (y : G true) :
    CoprodI.of x * (CoprodI.of y)⁻¹ ≠ (1 : CoprodI G) := by
  intro h
  apply hx
  have h2 : sourceRetraction G (CoprodI.of x * (CoprodI.of y)⁻¹) = 1 := by
    rw [h, map_one]
  rw [map_mul, map_inv, sourceRetraction_of_source, sourceRetraction_of_partner,
    inv_one, mul_one] at h2
  exact h2

end Retraction

/-! ## 1.  The relative design

Everything an explicit relator family over `U * B` has to satisfy, and nothing
that is a conclusion.  The constant is `1/7` and the length floor `42` because
that is the concrete pair `GreendlingerRelativeTransfer.fragmentSlack_of_le_seventh`
records: whole-syllable pieces are *weaker* than the classical Lyndon--Schupp
ones, so `C'(1/6)` at whole syllables buys nothing and the constant must drop
strictly below `1/6` first.

The design is stated over an arbitrary realization `G : Bool → Type` of the two
factors together with two isomorphisms, rather than over `factors U B` on the
nose.  That costs one composition at each use and buys freedom from every
definitional-unfolding question about the family. -/

/-- **The relative router design.**  A symmetrized metric small-cancellation
family of long cyclically reduced relators over a free product realizing `U` and
`B` as its two factors. -/
structure RelativeRouterDesign (U B : Type) [Group U] [Group B]
    (G : Bool → Type) [∀ b, Group (G b)] [∀ b, DecidableEq (G b)] where
  /-- The source factor is a copy of `U`. -/
  sourceEquiv : U ≃* G false
  /-- The partner factor is a copy of `B`. -/
  partnerEquiv : B ≃* G true
  /-- The relator family, as reduced syllable words. -/
  relators : Set (Word G)
  /-- Finitely many relators — the finite-presentation obligation. -/
  relators_finite : relators.Finite
  /-- The family is symmetrized: closed under cyclic rotation and formal
  inversion.  Without it the metric condition is vacuous for a one-element
  family and Dehn's algorithm has no competing occurrences. -/
  relators_symmetrized : Symmetrized relators
  /-- Every relator is cyclically reduced: its first and last syllables lie in
  different factors. -/
  relators_cyclicallyReduced : ∀ r ∈ relators, IsCyclicallyReduced r
  /-- **The length floor.**  `42` syllables is what `FragmentSlack` at `1/7`
  demands, since `1/6 - 1/7 = 1/42`. -/
  relators_long : ∀ r ∈ relators, 42 ≤ wlen r
  /-- No relator is a proper power.  Without it the quotient acquires torsion of
  its own; the symmetrized family of `(xy)^7` over `ℤ * ℤ` is the recorded
  witness. -/
  relators_noProperPower : NoProperPower relators
  /-- The metric condition, at the design's constant. -/
  metric : MetricSmallCancellation relators (1 / 7)

namespace RelativeRouterDesign

variable {U B : Type} [Group U] [Group B] {G : Bool → Type} [∀ b, Group (G b)]
  [∀ b, DecidableEq (G b)] (D : RelativeRouterDesign U B G)

/-- **The routed quotient** `(U * B) / ⟪R⟫`. -/
abbrev Routed : Type := CoprodI G ⧸ relatorSubgroup D.relators

/-- The fragment slack at the design's constant, from the length floor. -/
theorem fragmentSlack : FragmentSlack D.relators (1 / 7) :=
  fragmentSlack_of_le_seventh le_rfl D.relators_long

/-! ### The factors, and the ambient free product -/

include D in
/-- Both factors are torsion-free, transported from `U` and `B`.

`include D` because the *statement* does not mention the design — only the proof
does — and a section variable that the statement does not use is not in scope in
the body. -/
theorem factors_torsionFree (hU : IsPowerTorsionFree U) (hB : IsPowerTorsionFree B) :
    ∀ b, IsPowerTorsionFree (G b) := by
  intro b
  cases b
  · exact IsPowerTorsionFree.comap hU D.sourceEquiv.symm.toMonoidHom
      D.sourceEquiv.symm.injective
  · exact IsPowerTorsionFree.comap hB D.partnerEquiv.symm.toMonoidHom
      D.partnerEquiv.symm.injective

include D in
/-- Both factors are finitely presented, transported from `U` and `B`. -/
theorem factors_finitelyPresented [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] : ∀ b, Group.IsFinitelyPresented (G b) := by
  intro b
  cases b
  · exact Group.IsFinitelyPresented.equiv D.sourceEquiv
  · exact Group.IsFinitelyPresented.equiv D.partnerEquiv

include D in
/-- **The ambient free product is finitely presented**: two finitely presented
factors over a two-element index, which is
`FreeProductRouterObstruction.isFinitelyPresented_coprodI_bool` — the indexed
form of Mathlib's binary instance that the obstruction module supplies. -/
theorem ambient_finitelyPresented [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] : Group.IsFinitelyPresented (CoprodI G) := by
  haveI : Group.IsFinitelyPresented (G false) := D.factors_finitelyPresented false
  haveI : Group.IsFinitelyPresented (G true) := D.factors_finitelyPresented true
  exact FreeProductRouterObstruction.isFinitelyPresented_coprodI_bool G

/-- The relator subgroup is the normal closure of a finite set, by construction. -/
theorem relatorSubgroup_finitelyNormallyGenerated :
    (relatorSubgroup D.relators).IsFinitelyNormallyGenerated :=
  ⟨Word.prod '' D.relators, D.relators_finite.image _, rfl⟩

/-- **Finite presentation of the routed quotient, derived** — and it spends no
open leaf: finitely many relators over a finitely presented free product. -/
theorem finitelyPresented [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] : Group.IsFinitelyPresented D.Routed := by
  haveI := D.ambient_finitelyPresented
  exact Group.IsFinitelyPresented.quotient (relatorSubgroup D.relators)
    D.relatorSubgroup_finitelyNormallyGenerated

/-! ## 2.  The two maps -/

/-- **The source's map into the routed quotient**, the candidate embedding. -/
def emb : U →* D.Routed :=
  (factorMap (relatorSubgroup D.relators) false).comp D.sourceEquiv.toMonoidHom

/-- **The partner's map into the routed quotient.** -/
def partnerHom : B →* D.Routed :=
  (factorMap (relatorSubgroup D.relators) true).comp D.partnerEquiv.toMonoidHom

theorem emb_apply (x : U) :
    D.emb x = QuotientGroup.mk' (relatorSubgroup D.relators)
      (CoprodI.of (D.sourceEquiv x)) := rfl

theorem partnerHom_apply (x : B) :
    D.partnerHom x = QuotientGroup.mk' (relatorSubgroup D.relators)
      (CoprodI.of (D.partnerEquiv x)) := rfl

/-! ## 3.  The small-cancellation conclusions

One call to `GreendlingerRelativeTransfer.osin_conclusion_of_metric`, whose two
open leaves stand in every binder list below. -/

/-- **The whole conclusion list of the relative small-cancellation theorem**, at
this design's data: the Greendlinger length bound, the torsion classification,
the embedding clause for *both* factors, and torsion-freeness of the quotient. -/
theorem osinConclusions (hleafG : RelativeGreendlingerLeaf D.relators (1 / 7))
    (hleafT : RelativeTorsionLeaf D.relators (1 / 7))
    (hU : IsPowerTorsionFree U) (hB : IsPowerTorsionFree B) :
    GreendlingerLengthBound D.relators ∧
      TorsionIntoFactors (relatorSubgroup D.relators) ∧
      (∀ b, Function.Injective (factorMap (relatorSubgroup D.relators) b)) ∧
      IsPowerTorsionFree D.Routed :=
  osin_conclusion_of_metric hleafG hleafT D.relators_symmetrized
    D.relators_cyclicallyReduced D.relators_long D.metric D.relators_noProperPower
    (D.factors_torsionFree hU hB)

/-- The Greendlinger length bound, from the length leaf alone. -/
theorem lengthBound (hleafG : RelativeGreendlingerLeaf D.relators (1 / 7)) :
    GreendlingerLengthBound D.relators :=
  greendlingerLengthBound_of_slack hleafG D.relators_symmetrized
    D.relators_cyclicallyReduced D.fragmentSlack D.metric

/-- **The source embeds**, given the length bound.  This is the free-product
Greendlinger factor-embedding clause at the source index; nothing about that
index is special, which is the whole trouble in section 5. -/
theorem emb_injective (hlen : GreendlingerLengthBound D.relators) :
    Function.Injective D.emb :=
  (factorMap_injective_of_cyclicallyReduced hlen D.relators_cyclicallyReduced
    false).comp D.sourceEquiv.injective

/-- The partner embeds too, by the same clause at the other index. -/
theorem partnerHom_injective (hlen : GreendlingerLengthBound D.relators) :
    Function.Injective D.partnerHom :=
  (factorMap_injective_of_cyclicallyReduced hlen D.relators_cyclicallyReduced
    true).comp D.partnerEquiv.injective

/-- **The routed quotient is torsion-free**, from both leaves and
torsion-freeness of the two factors. -/
theorem torsionFree (hleafG : RelativeGreendlingerLeaf D.relators (1 / 7))
    (hleafT : RelativeTorsionLeaf D.relators (1 / 7))
    (hU : IsPowerTorsionFree U) (hB : IsPowerTorsionFree B) :
    IsPowerTorsionFree D.Routed :=
  (D.osinConclusions hleafG hleafT hU hB).2.2.2

/-- **Property `(T)` from a surjection of the partner**, the shape the routing
interface uses (`SmallCancellationRouter.RoutingLemmaData.kazhdan`).  It is
stated because it is the only mechanism available and because section 5 needs it
stated in order to refute its hypothesis: nothing in this repository derives
`hsurj` for a design, and `not_partnerSurjective` proves nothing can. -/
theorem kazhdan_of_partnerSurjective (hB : HasKazhdanPropertyT.{0, 0} B)
    (hsurj : Function.Surjective D.partnerHom) :
    HasKazhdanPropertyT.{0, 0} D.Routed :=
  HasKazhdanPropertyT.of_surjective D.partnerHom hsurj hB

/-! ## 4.  The envelope

Three clauses are derived; property `(T)` is a hypothesis, for the reason
section 5 proves. -/

/-- **A Kazhdan envelope of `U` from a relative router design.**

Finite presentation, torsion-freeness and the embedding are all conclusions.
Property `(T)` of the routed quotient is the single remaining hypothesis, and it
is not an oversight: `not_partnerSurjective` below shows that the one route to
it available in the whole-syllable framework — making the partner's image fill
the quotient — contradicts the design's own length floor. -/
noncomputable def kazhdanEnvelope_of_design [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B]
    (hleafG : RelativeGreendlingerLeaf D.relators (1 / 7))
    (hleafT : RelativeTorsionLeaf D.relators (1 / 7))
    (hU : IsPowerTorsionFree U) (hBtf : IsPowerTorsionFree B)
    (hT : HasKazhdanPropertyT.{0, 0} D.Routed) : KazhdanEnvelope U where
  Carrier := D.Routed
  finitelyPresentedCarrier := D.finitelyPresented
  torsionFree := D.torsionFree hleafG hleafT hU hBtf
  kazhdan := hT
  emb := D.emb
  emb_injective := D.emb_injective (D.lengthBound hleafG)

end RelativeRouterDesign

/-! ## 5.  The tie route, refuted

A *tie* is a relation identifying a source element with a partner element.  It
is what makes the partner's image fill the quotient, hence the only route to
property `(T)`, and it is exactly what the syllable metric forbids. -/

section Tie

variable {G : Bool → Type} [∀ b, Group (G b)] [∀ b, DecidableEq (G b)]

omit [∀ b, DecidableEq (G b)] in
/-- A relator subgroup member of the shape `a · b⁻¹` identifies `a` with `b` in
the quotient.  This is the only way a tie is ever used.

The decidable-equality instances are omitted because `relatorSubgroup` does not
consume them; only the syllable-length lemmas below do. -/
theorem mk_eq_mk_of_tie {R : Set (Word G)} {a c : CoprodI G}
    (h : a * c⁻¹ ∈ relatorSubgroup R) :
    QuotientGroup.mk' (relatorSubgroup R) a
      = QuotientGroup.mk' (relatorSubgroup R) c := by
  have h1 : QuotientGroup.mk' (relatorSubgroup R) (a * c⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

/-- **A tie is short.**  A source syllable times the inverse of a partner
syllable has syllable length at most two, whatever the two elements are:
syllable length is subadditive and a single syllable has length at most one. -/
theorem sylLength_tie_le (x : G false) (y : G true) :
    FreeProductCyclic.sylLength (CoprodI.of x * (CoprodI.of y)⁻¹) ≤ 2 := by
  have ha := FreeProductCyclic.sylLength_mul_le (CoprodI.of x) ((CoprodI.of y)⁻¹)
  have hb := FreeProductCyclic.sylLength_of_le_one x
  have hc : FreeProductCyclic.sylLength ((CoprodI.of y)⁻¹)
      = FreeProductCyclic.sylLength (CoprodI.of y) :=
    FreeProductCyclic.sylLength_inv _
  have hd := FreeProductCyclic.sylLength_of_le_one y
  omega

/-- **The collision, unconditionally.**  A family all of whose relators have at
least four syllables cannot tie a nonidentity source element to a partner
element and still satisfy the Greendlinger length bound: the tie is a
nonidentity relator subgroup member of syllable length at most two, and the
bound would produce a relator shorter than four.

The design's own floor is `42`, so this applies to every relative router design;
and `42` is not a slack choice — `FragmentSlack` at any constant below `1/6`
forces a floor of at least six, and at `1/6` itself no floor works at all. -/
theorem not_greendlingerLengthBound_of_tie {R : Set (Word G)} {x : G false}
    {y : G true} (hx : x ≠ 1) (hlong : ∀ r ∈ R, 4 ≤ wlen r)
    (htie : CoprodI.of x * (CoprodI.of y)⁻¹ ∈ relatorSubgroup R) :
    ¬ GreendlingerLengthBound R := by
  intro hG
  obtain ⟨r, hr, hlt⟩ := hG _ (tieWord_ne_one hx y) htie
  have h1 := sylLength_tie_le x y
  have h2 := hlong r hr
  omega

end Tie

namespace RelativeRouterDesign

variable {U B : Type} [Group U] [Group B] {G : Bool → Type} [∀ b, Group (G b)]
  [∀ b, DecidableEq (G b)] (D : RelativeRouterDesign U B G)

/-- **A surjective partner map is a tie, at every source element.**  If the
partner's image fills the quotient then in particular it catches the image of
each source syllable, and catching it is a relator subgroup membership of the
tying shape. -/
theorem exists_tie_of_partnerSurjective (hsurj : Function.Surjective D.partnerHom)
    (x : G false) :
    ∃ y : G true,
      CoprodI.of x * (CoprodI.of y)⁻¹ ∈ relatorSubgroup D.relators := by
  obtain ⟨c, hc⟩ := hsurj (QuotientGroup.mk' (relatorSubgroup D.relators)
    (CoprodI.of x))
  refine ⟨D.partnerEquiv c, ?_⟩
  have h1 : QuotientGroup.mk' (relatorSubgroup D.relators)
      (CoprodI.of (D.partnerEquiv c))
      = QuotientGroup.mk' (relatorSubgroup D.relators) (CoprodI.of x) := hc
  rw [← QuotientGroup.eq_one_iff]
  show QuotientGroup.mk' (relatorSubgroup D.relators)
    (CoprodI.of x * (CoprodI.of (D.partnerEquiv c))⁻¹) = 1
  rw [map_mul, map_inv, h1, mul_inv_cancel]

/-- **The collapse.**  If the partner's image fills the quotient then, the
length bound being what the design's leaf delivers, the partner map is injective
as well — so it is an isomorphism onto the routed quotient
(`FreeProductRouterObstruction.factorMap_bijective_of_surjective` is the same
observation at the factor map), and the source embeds in the *partner*.

Read at `B = Γ(3)` this says the route can only ever produce envelopes of groups
that already sit inside `Γ(3)`. -/
theorem exists_injective_to_partner (hlen : GreendlingerLengthBound D.relators)
    (hsurj : Function.Surjective D.partnerHom) :
    ∃ f : U →* B, Function.Injective f := by
  have hbij : Function.Bijective D.partnerHom :=
    ⟨D.partnerHom_injective hlen, hsurj⟩
  refine ⟨(MulEquiv.ofBijective D.partnerHom hbij).symm.toMonoidHom.comp D.emb, ?_⟩
  exact (MulEquiv.ofBijective D.partnerHom hbij).symm.injective.comp
    (D.emb_injective hlen)

/-- **What the collapse would cost.**  A universal source transported through the
collapse makes the *partner* universal for finitely presented torsion-free
groups.  At `B = Γ(3)` that is false — `Γ(3) ≤ SL₃(ℤ)` is residually finite,
while Higman's group is finitely presented, torsion-free and has no nontrivial
finite quotient — so the hypothesis list of this theorem is unsatisfiable there.
`not_partnerSurjective` refutes it directly and with no appeal to any property of
the partner at all. -/
theorem partner_universal_of_partnerSurjective
    (huniv : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* U, Function.Injective f)
    (hlen : GreendlingerLengthBound D.relators)
    (hsurj : Function.Surjective D.partnerHom) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* B, Function.Injective f := by
  obtain ⟨f, hf⟩ := D.exists_injective_to_partner hlen hsurj
  exact universal_comp huniv f hf

/-- **The refutation.**  Whenever the source has a nonidentity element, the
partner map of a relative router design is never onto.

So `kazhdan_of_partnerSurjective` has no instance at a nontrivial source, and
property `(T)` of the routed quotient is not obtainable from the design.  This
is the theorem that makes the `hT` hypothesis of `kazhdanEnvelope_of_design`
irreducible rather than lazy. -/
theorem not_partnerSurjective (hlen : GreendlingerLengthBound D.relators) {x : U}
    (hx : x ≠ 1) : ¬ Function.Surjective D.partnerHom := by
  intro hsurj
  have hx' : D.sourceEquiv x ≠ (1 : G false) := by
    intro h
    exact hx (D.sourceEquiv.injective (by rw [h, map_one]))
  obtain ⟨y, hy⟩ := D.exists_tie_of_partnerSurjective hsurj (D.sourceEquiv x)
  refine not_greendlingerLengthBound_of_tie (y := y) hx' ?_ hy hlen
  intro r hr
  have h42 := D.relators_long r hr
  omega

/-- The refutation with the leaf in place of the bound it delivers, which is the
shape a caller who only has a design will have. -/
theorem not_partnerSurjective_of_leaf
    (hleafG : RelativeGreendlingerLeaf D.relators (1 / 7)) {x : U} (hx : x ≠ 1) :
    ¬ Function.Surjective D.partnerHom :=
  D.not_partnerSurjective (D.lengthBound hleafG) hx

/-- **No tie at all**, in the form a word design would want to check: no
nonidentity source element is identified with any partner element. -/
theorem not_tie (hlen : GreendlingerLengthBound D.relators) {x : U} (hx : x ≠ 1)
    (y : B) :
    CoprodI.of (D.sourceEquiv x) * (CoprodI.of (D.partnerEquiv y))⁻¹
      ∉ relatorSubgroup D.relators := by
  intro htie
  have hx' : D.sourceEquiv x ≠ (1 : G false) := by
    intro h
    exact hx (D.sourceEquiv.injective (by rw [h, map_one]))
  refine not_greendlingerLengthBound_of_tie hx' ?_ htie hlen
  intro r hr
  have h42 := D.relators_long r hr
  omega

end RelativeRouterDesign

/-! ## 6.  The word-level blueprint

The free lane's `Sofic.AvatarWordFamily` turns a finite presentation of the
source and of the partner into an explicit relator family over the two-generator
free group, and leaves four word-level checks as named hypotheses.  This section
is the relative analogue's data layer: a finite *list* of syllable words, so
that finiteness is free, together with finite generating tuples of both groups —
the raw material an exponent-code avatar family is written in.

Six obligations are named.  Five of them are the design's word-level fields, all
decidable by inspection of the finitely many relators.  The sixth is the partner
tie, which is what an avatar family would have to produce in order to reach
property `(T)`, and `not_partnerTieObligation` proves it has no inhabitant. -/

section Blueprint

/-- A finite generating tuple.  This is the fragment of a finite presentation the
tie obligation is stated over. -/
structure FiniteGeneration (H : Type) [Group H] where
  /-- The number of generators. -/
  card : ℕ
  /-- The generators. -/
  gen : Fin card → H
  /-- They generate. -/
  generates : Subgroup.closure (Set.range gen) = ⊤

/-- **Every finitely presented group has a finite generating tuple**, from the
presentation map of `Group.IsFinitelyPresented`. -/
theorem nonempty_finiteGeneration (H : Type) [Group H]
    [h : Group.IsFinitelyPresented H] : Nonempty (FiniteGeneration H) := by
  obtain ⟨n, φ, hφ, -⟩ := h.out
  refine ⟨⟨n, fun k => φ (FreeGroup.of k), ?_⟩⟩
  have hmap := MonoidHom.map_closure φ
    (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)))
  rw [FreeGroup.closure_range_of, Subgroup.map_top_of_surjective φ hφ] at hmap
  have hrange : ⇑φ '' Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))
      = Set.range fun k => φ (FreeGroup.of k) := by
    ext z
    constructor
    · rintro ⟨-, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨FreeGroup.of k, ⟨k, rfl⟩, rfl⟩
  rw [hmap, hrange]

/-- A choice of finite generating tuple. -/
noncomputable def finiteGeneration (H : Type) [Group H]
    [Group.IsFinitelyPresented H] : FiniteGeneration H :=
  (nonempty_finiteGeneration H).some

/-- **A finite generating tuple of the certified partner `Γ(3)`**, extracted by
choice from `gamma3Partner`'s finite presentation.  Nothing is assumed:
`CongruenceSubgroup.gamma3_finitelyPresented` is the thirteen-relator
presentation of `SL₃(ℤ)` together with the in-repo Reidemeister--Schreier
descent.  This is the alphabet an exponent-code avatar family over the partner
factor would be written in. -/
noncomputable def gamma3Generation :
    FiniteGeneration CongruenceSubgroup.gamma3Partner.B :=
  finiteGeneration _

/-- **The word-level blueprint.**  The relator family is a finite list, so
finiteness is a theorem rather than an obligation, and both groups come with a
finite generating tuple so that the tie obligation is a statement about finitely
many words. -/
structure RelativeAvatarBlueprint (U B : Type) [Group U] [Group B]
    (G : Bool → Type) [∀ b, Group (G b)] [∀ b, DecidableEq (G b)] where
  /-- The source factor is a copy of `U`. -/
  sourceEquiv : U ≃* G false
  /-- The partner factor is a copy of `B`. -/
  partnerEquiv : B ≃* G true
  /-- A finite generating tuple of the source. -/
  sourceGen : FiniteGeneration U
  /-- A finite generating tuple of the partner. -/
  partnerGen : FiniteGeneration B
  /-- The relator family, as an explicit list. -/
  relatorList : List (Word G)

namespace RelativeAvatarBlueprint

variable {U B : Type} [Group U] [Group B] {G : Bool → Type} [∀ b, Group (G b)]
  [∀ b, DecidableEq (G b)] (P : RelativeAvatarBlueprint U B G)

/-- The relator family of a blueprint. -/
def relators : Set (Word G) := {r | r ∈ P.relatorList}

/-- **Finiteness is free**, the family being a list. -/
theorem relators_finite : P.relators.Finite :=
  P.relatorList.finite_toSet

/-- **The five word-level checks.**  Everything about the relator list that the
blueprint does not decide, each a statement about the finitely many members of
one explicit list.

`primeLength` is the designable form of the no-proper-power condition: a
cyclically reduced relator whose syllable count is prime is not a proper power,
by `GreendlingerRelativeTransfer.noProperPower_of_prime_wlen`, and counting
syllables is something a relator design controls by construction. -/
structure Obligations : Prop where
  /-- Closed under cyclic rotation and formal inversion. -/
  symmetrized : Symmetrized P.relators
  /-- First and last syllables in different factors. -/
  cyclicallyReduced : ∀ r ∈ P.relators, IsCyclicallyReduced r
  /-- The fragment-slack length floor. -/
  long : ∀ r ∈ P.relators, 42 ≤ wlen r
  /-- A prime syllable count, which rules out proper powers. -/
  primeLength : ∀ r ∈ P.relators, Nat.Prime (wlen r)
  /-- The metric condition at the design's constant. -/
  metric : MetricSmallCancellation P.relators (1 / 7)

/-- **The design, assembled.**  Finiteness is the blueprint's own theorem, the
no-proper-power field is the prime-syllable criterion spent once, and the
remaining four fields are the obligations verbatim. -/
def design (H : P.Obligations) : RelativeRouterDesign U B G where
  sourceEquiv := P.sourceEquiv
  partnerEquiv := P.partnerEquiv
  relators := P.relators
  relators_finite := P.relators_finite
  relators_symmetrized := H.symmetrized
  relators_cyclicallyReduced := H.cyclicallyReduced
  relators_long := H.long
  relators_noProperPower :=
    noProperPower_of_prime_wlen H.cyclicallyReduced H.primeLength
  metric := H.metric

/-- The design's family is the blueprint's, on the nose — so a hypothesis about
one is a hypothesis about the other with no transport. -/
theorem design_relators (H : P.Obligations) :
    (P.design H).relators = P.relators := rfl

/-- **The sixth obligation: the partner tie.**  Each source generator is
identified, modulo the relators, with an element of the partner factor.  This is
what an avatar family over the partner's generators would have to deliver, and
it is the only route to property `(T)` in this framework — it is exactly what
makes the partner's image fill the quotient. -/
def PartnerTieObligation : Prop :=
  ∀ k : Fin P.sourceGen.card, ∃ y : G true,
    CoprodI.of (P.sourceEquiv (P.sourceGen.gen k)) * (CoprodI.of y)⁻¹
      ∈ relatorSubgroup P.relators

/-- The source generators, transported into the source factor, generate it. -/
theorem closure_sourceGen :
    Subgroup.closure (Set.range fun k => P.sourceEquiv (P.sourceGen.gen k))
      = (⊤ : Subgroup (G false)) := by
  have hsurj : Function.Surjective ⇑P.sourceEquiv.toMonoidHom :=
    P.sourceEquiv.surjective
  have hmap := MonoidHom.map_closure P.sourceEquiv.toMonoidHom
    (Set.range P.sourceGen.gen)
  rw [P.sourceGen.generates,
    Subgroup.map_top_of_surjective P.sourceEquiv.toMonoidHom hsurj] at hmap
  have hrange : ⇑P.sourceEquiv.toMonoidHom '' Set.range P.sourceGen.gen
      = Set.range fun k => P.sourceEquiv (P.sourceGen.gen k) := by
    ext z
    constructor
    · rintro ⟨-, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨P.sourceGen.gen k, ⟨k, rfl⟩, rfl⟩
  rw [hrange] at hmap
  exact hmap.symm

/-- Under the tie obligation, every source syllable already lies in the partner's
image: the tie holds on a generating set, and lying in the partner's image is a
subgroup condition. -/
theorem mem_range_partnerHom_of_source (H : P.Obligations)
    (htie : P.PartnerTieObligation) (x : G false) :
    QuotientGroup.mk' (relatorSubgroup P.relators) (CoprodI.of x)
      ∈ (P.design H).partnerHom.range := by
  have hsub : (⊤ : Subgroup (G false)) ≤
      ((P.design H).partnerHom.range).comap
        (factorMap (relatorSubgroup P.relators) false) := by
    rw [← P.closure_sourceGen, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨y, hy⟩ := htie k
    refine ⟨P.partnerEquiv.symm y, ?_⟩
    have h1 : (P.design H).partnerHom (P.partnerEquiv.symm y)
        = QuotientGroup.mk' (relatorSubgroup P.relators) (CoprodI.of y) := by
      show QuotientGroup.mk' (relatorSubgroup P.relators)
        (CoprodI.of (P.partnerEquiv (P.partnerEquiv.symm y))) = _
      rw [MulEquiv.apply_symm_apply]
    rw [h1]
    exact (mk_eq_mk_of_tie hy).symm
  exact hsub (Subgroup.mem_top x)

/-- **The tie obligation does make the partner fill the quotient.**  Both
factors' syllables land in the partner's image — the partner's own trivially,
the source's by the tie — and they generate the free product. -/
theorem partnerHom_surjective (H : P.Obligations) (htie : P.PartnerTieObligation) :
    Function.Surjective (P.design H).partnerHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  rintro q -
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (relatorSubgroup P.relators) q
  induction g using CoprodI.induction_on with
  | one =>
      rw [map_one]
      exact one_mem _
  | of b x =>
      cases b
      · exact P.mem_range_partnerHom_of_source H htie x
      · refine ⟨P.partnerEquiv.symm x, ?_⟩
        show QuotientGroup.mk' (relatorSubgroup P.relators)
          (CoprodI.of (P.partnerEquiv (P.partnerEquiv.symm x))) = _
        rw [MulEquiv.apply_symm_apply]
  | mul u v hu hv =>
      rw [map_mul]
      exact mul_mem hu hv

/-- **Property `(T)` would follow from the sixth obligation.**  Recorded so that
the refutation below is visibly a refutation of the *only* available route, and
not of a route chosen to be easy to refute. -/
theorem kazhdan_of_partnerTie (H : P.Obligations) (htie : P.PartnerTieObligation)
    (hB : HasKazhdanPropertyT.{0, 0} B) :
    HasKazhdanPropertyT.{0, 0} (P.design H).Routed :=
  (P.design H).kazhdan_of_partnerSurjective hB (P.partnerHom_surjective H htie)

/-- **The sixth obligation has no inhabitant.**  Given the length bound the
design's leaf delivers, and one nonidentity element of the source, no blueprint
satisfies the partner tie.

This is the whole content of section 5 restated at the blueprint: an exponent-code
avatar family over the partner's generators cannot exist, because a word in the
partner's generators is a *single syllable* of the free product, so the tie
relator has two syllables and the family's own floor is `42`. -/
theorem not_partnerTieObligation (H : P.Obligations)
    (hlen : GreendlingerLengthBound P.relators) {x : U} (hx : x ≠ 1) :
    ¬ P.PartnerTieObligation := by
  intro htie
  exact (P.design H).not_partnerSurjective hlen hx (P.partnerHom_surjective H htie)

/-- The refutation with the leaf in place of the bound it delivers. -/
theorem not_partnerTieObligation_of_leaf (H : P.Obligations)
    (hleafG : RelativeGreendlingerLeaf P.relators (1 / 7)) {x : U} (hx : x ≠ 1) :
    ¬ P.PartnerTieObligation :=
  P.not_partnerTieObligation H ((P.design H).lengthBound hleafG) hx

/-- **The envelope from a blueprint**, with the property-`(T)` clause carried as
the hypothesis section 5 shows it has to be. -/
noncomputable def kazhdanEnvelope [Group.IsFinitelyPresented U]
    [Group.IsFinitelyPresented B] (H : P.Obligations)
    (hleafG : RelativeGreendlingerLeaf P.relators (1 / 7))
    (hleafT : RelativeTorsionLeaf P.relators (1 / 7))
    (hU : IsPowerTorsionFree U) (hBtf : IsPowerTorsionFree B)
    (hT : HasKazhdanPropertyT.{0, 0} (P.design H).Routed) : KazhdanEnvelope U :=
  (P.design H).kazhdanEnvelope_of_design hleafG hleafT hU hBtf hT

end RelativeAvatarBlueprint

end Blueprint

/-! ## 7.  The certified partner, in the shape the blueprint consumes

`CongruenceSubgroup.gamma3Partner` is the fully certified torsion-free finitely
presented Kazhdan partner: property `(T)` from the exact rational Hodge
certificate through finite-index permanence, torsion-freeness from Minkowski at
level three, finite presentation from the P13 descent and
Reidemeister--Schreier.  These three declarations name its fields at the types
this module's theorems ask for, so a blueprint over `Γ(3)` never has to reopen
`Kazhdan/TorsionFreeKazhdanPartner.lean`. -/

/-- The partner's torsion-freeness, at the type `factors_torsionFree` consumes. -/
theorem gamma3_torsionFree :
    IsPowerTorsionFree CongruenceSubgroup.gamma3Partner.B :=
  CongruenceSubgroup.gamma3Partner.torsionFree

/-- The partner's property `(T)`, at the type `kazhdan_of_partnerSurjective`
consumes — and, by `RelativeRouterDesign.not_partnerSurjective`, the field this
module can never actually spend. -/
theorem gamma3_kazhdan :
    HasKazhdanPropertyT.{0, 0} CongruenceSubgroup.gamma3Partner.B :=
  CongruenceSubgroup.gamma3Partner.kazhdan

/-- The partner's finite presentation.  Stated rather than registered:
`TorsionFreeKazhdanPartner.instFinitelyPresented` already supplies the instance,
so a blueprint over `Γ(3)` gets it by search. -/
theorem gamma3_finitelyPresented :
    Group.IsFinitelyPresented CongruenceSubgroup.gamma3Partner.B :=
  CongruenceSubgroup.gamma3Partner.finitelyPresented

end RelativeRouterEnvelope
end GroupApproximation
