import GroupApproximation.Sofic.FournierFacioUniversalGroup
import GroupApproximation.Algebra.Amenable
import GroupApproximation.Algebra.HyperbolicGroup
import GroupApproximation.Analysis.PropertyTNonamenable

/-!
# Typed interfaces for the small-cancellation Kazhdan envelope

The manuscript now uses a Fournier-Facio--Hull--Osin small-cancellation
argument to obtain a torsion-free finitely presented non-MF group.  This module
does not formalize those literature theorems or construct their groups.
Instead it records the input and output clauses of the route as typed
interfaces and proves the consequences that follow once those interfaces are
supplied.

`HyperbolicKazhdanPartner` packages the infinite finitely presented
torsion-free hyperbolic property-(T) partner.  `SmallCancellationQuotient U H`
packages the quotient of `U * H` in which `U` embeds, the partner surjects, and
finite presentation and torsion-freeness are preserved.  Property (T) of the
output is derived from the partner's surjection rather than stored as a field.

No inhabitant of either interface is constructed here.  Accordingly, this
module is not a Lean proof of the manuscript's paper-level existence theorem;
it is a formal description of the theorem's boundary.  The final
normal-Kazhdan obstruction, once the group-theoretic data are supplied, is
formalized elsewhere.
-/

namespace GroupApproximation
namespace SmallCancellationEnvelope

open scoped Monoid.Coprod

open FournierFacioUniversal

/-! ## 1.  The hyperbolic Kazhdan partner -/

/-- **The second group of the small-cancellation pair.**  An infinite finitely
presented torsion-free hyperbolic group with property `(T)`, supplied by random
groups at density below `1/2`.

**Hyperbolicity is now a field.**  It was not one when this module was written,
because the library could not state the notion; `Algebra/HyperbolicGroup.lean`
supplies it --- Gromov's four-point condition on the word metric of a finite
symmetric generating set --- so the interface can record what the literature
actually delivers instead of the fragment the route happens to consume.

**Infiniteness is a field, and it is what keeps the interface honest.**  Every
other clause holds of the trivial group: a finite group is hyperbolic
(`Hyperbolic.isHyperbolicGroup_of_finite`) and Kazhdan, and a finite group is
torsion-free exactly when it is trivial.  Without this clause the structure
would be inhabited by a group the small-cancellation step cannot use, and
`KC.21` would read as discharged by a witness that discharges nothing.  With
it, `HyperbolicKazhdanPartner.not_isAmenable` derives that the partner is
nonelementary.

Torsion-freeness is recorded because it is what makes the free product `U * H`
torsion-free, which is what Osin's torsion-preservation clause preserves. -/
structure HyperbolicKazhdanPartner where
  /-- The partner `H`. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresentedCarrier : Group.IsFinitelyPresented Carrier]
  [infiniteCarrier : Infinite Carrier]
  /-- `H` is torsion-free. -/
  torsionFree : IsPowerTorsionFree Carrier
  /-- `H` is hyperbolic, in the four-point sense of
  `Algebra/HyperbolicGroup.lean`. -/
  hyperbolic : Hyperbolic.IsHyperbolicGroup Carrier
  /-- `H` has property `(T)`; this is the sole source of `(T)` downstream. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier

instance partnerGroup (H : HyperbolicKazhdanPartner) : Group H.Carrier :=
  H.groupCarrier

instance partnerFinitelyPresented (H : HyperbolicKazhdanPartner) :
    Group.IsFinitelyPresented H.Carrier :=
  H.finitelyPresentedCarrier

instance partnerInfinite (H : HyperbolicKazhdanPartner) : Infinite H.Carrier :=
  H.infiniteCarrier

/-- **The partner is nonamenable**, derived from the two fields and not
postulated: an infinite Kazhdan group is not amenable
(`PropertyTNonamenable.infinite_kazhdan_not_isAmenable`).

This is the checkable half of nonelementarity.  The elementary hyperbolic groups
are the virtually cyclic ones, and those are amenable, so a nonamenable
hyperbolic group is nonelementary --- which is what Osin's small cancellation
over `(U * H, U)` needs of the partner.  That last step is the standard fact
about virtually cyclic groups; this library does not state it, so what is
recorded here is nonamenability alone. -/
theorem HyperbolicKazhdanPartner.not_isAmenable (H : HyperbolicKazhdanPartner) :
    ¬ Amenability.IsAmenable H.Carrier :=
  PropertyTNonamenable.infinite_kazhdan_not_isAmenable H.kazhdan

/-! ## 2.  The small-cancellation common quotient -/

/-- **The output of the small-cancellation step over `(U * H, U)`.**

A quotient `Q` of the free product in which

* the peripheral factor `U` still embeds --- this is what small cancellation
  over a relatively hyperbolic group buys, and it is the clause that makes
  the envelope an envelope;
* the Kazhdan partner surjects --- this is the common-quotient clause, and it
  is where property `(T)` of `Q` comes from;
* torsion-freeness survives --- Osin, Theorem 2.4.5;
* finite presentation survives.

Nothing inhabits this structure.  Every declaration below takes one as an
explicit argument. -/
structure SmallCancellationQuotient (U H : Type) [Group U] [Group H] where
  /-- The small-cancellation quotient `Q` of `U * H`. -/
  Quotient : Type
  [groupQuotient : Group Quotient]
  [finitelyPresented : Group.IsFinitelyPresented Quotient]
  /-- The image of the peripheral factor. -/
  fromPeripheral : U →* Quotient
  /-- The peripheral factor embeds. -/
  fromPeripheral_injective : Function.Injective fromPeripheral
  /-- The image of the Kazhdan partner. -/
  fromPartner : H →* Quotient
  /-- The partner's image is everything. -/
  fromPartner_surjective : Function.Surjective fromPartner
  /-- Osin's torsion-preservation clause. -/
  torsionFree : IsPowerTorsionFree Quotient

/-- **The source of the small-cancellation step is itself finitely
presented**, so the route stays inside the finitely presented world from
beginning to end. -/
theorem coprod_finitelyPresented {U H : Type} [Group U] [Group H]
    [Group.IsFinitelyPresented U] [Group.IsFinitelyPresented H] :
    Group.IsFinitelyPresented (U ∗ H) :=
  inferInstance

namespace SmallCancellationQuotient

instance quotientGroup {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H) : Group C.Quotient :=
  C.groupQuotient

instance quotientFinitelyPresented {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H) :
    Group.IsFinitelyPresented C.Quotient :=
  C.finitelyPresented

/-- **The quotient really is a quotient of the free product.**  The two
factor maps assemble into one homomorphism out of `U * H`, which is the
object the phrase "small cancellation over `U * H`" is about. -/
def liftMap {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H) : (U ∗ H) →* C.Quotient :=
  Monoid.Coprod.lift C.fromPeripheral C.fromPartner

@[simp] theorem liftMap_inl {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H) (u : U) :
    C.liftMap (Monoid.Coprod.inl u) = C.fromPeripheral u := rfl

@[simp] theorem liftMap_inr {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H) (h : H) :
    C.liftMap (Monoid.Coprod.inr h) = C.fromPartner h := rfl

/-- The quotient map out of the free product is onto, already because the
partner alone is onto. -/
theorem liftMap_surjective {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H) : Function.Surjective C.liftMap := by
  intro y
  obtain ⟨h, hh⟩ := C.fromPartner_surjective y
  exact ⟨Monoid.Coprod.inr h, (C.liftMap_inr h).trans hh⟩

/-- **Property `(T)` of the quotient, derived and not assumed.**  A quotient
of a Kazhdan group is Kazhdan --- `HasKazhdanPropertyT.of_surjective` pushes a
Kazhdan pair forward along the epimorphism --- and the partner surjects, so
the small-cancellation quotient inherits `(T)` from the hyperbolic partner
and from nothing else. -/
theorem kazhdan {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H)
    (hH : HasKazhdanPropertyT.{0, 0} H) :
    HasKazhdanPropertyT.{0, 0} C.Quotient :=
  HasKazhdanPropertyT.of_surjective C.fromPartner C.fromPartner_surjective hH

/-- **The route's output is an envelope.**  Assembling the four clauses of
`KazhdanEnvelope` from the three clauses of the small-cancellation quotient
plus the partner's property `(T)`. -/
def toKazhdanEnvelope {U H : Type} [Group U] [Group H]
    (C : SmallCancellationQuotient U H)
    (hH : HasKazhdanPropertyT.{0, 0} H) : KazhdanEnvelope U where
  Carrier := C.Quotient
  groupCarrier := C.groupQuotient
  finitelyPresentedCarrier := C.finitelyPresented
  torsionFree := C.torsionFree
  kazhdan := C.kazhdan hH
  emb := C.fromPeripheral
  emb_injective := C.fromPeripheral_injective

end SmallCancellationQuotient

/-- The route, with the partner packaged: a small-cancellation quotient over
`(U * H, U)` is a Kazhdan envelope of `U`. -/
def kazhdanEnvelope (U : Type) [Group U] (H : HyperbolicKazhdanPartner)
    (C : SmallCancellationQuotient U H.Carrier) : KazhdanEnvelope U :=
  C.toKazhdanEnvelope H.kazhdan

/-! ## 3.  `KC.21` by the small-cancellation route -/

/-- **Fournier-Facio's group, built by the route `LI.12b` points at.**

From a universal finitely presented torsion-free group, a torsion-free
hyperbolic Kazhdan partner, and a small-cancellation quotient of their free
product with the four clauses above, one gets a finitely presented
torsion-free property-`(T)` group containing a copy of every finitely
presented torsion-free group.

Everything between the inputs and this conclusion is machine-checked:
property `(T)` through `HasKazhdanPropertyT.of_surjective`, universality
through `FournierFacioUniversal.universal_comp`, and nothing else is
required.  Compose with
`FournierFacioUniversal.realization_of_universalKazhdanGroup` for the printed
remark. -/
def universalKazhdanGroup (Host : UniversalTorsionFreeHost)
    (H : HyperbolicKazhdanPartner)
    (C : SmallCancellationQuotient Host.Carrier H.Carrier) :
    UniversalKazhdanGroup :=
  UniversalKazhdanGroup.ofInputs Host (kazhdanEnvelope Host.Carrier H C)

/-- The group produced by the route is the small-cancellation quotient
itself; the host contributes universality and the partner contributes
property `(T)`, and neither contributes a new carrier. -/
@[simp]
theorem universalKazhdanGroup_carrier (Host : UniversalTorsionFreeHost)
    (H : HyperbolicKazhdanPartner)
    (C : SmallCancellationQuotient Host.Carrier H.Carrier) :
    (universalKazhdanGroup Host H C).Carrier = C.Quotient := rfl

/-! ## 4.  The neighbouring citation, and the single clause it lacks -/

/-- **Chatterji--Kassabov, Theorem 3**, at a finitely presented source: an
embedding into a finitely presented property-`(T)` group normally generated
by a prescribed element.

This is recorded as established from source in the research graph
(`research/chatterji-kassabov-normal-generator-embedding.md`,
arXiv:2601.22907), and it is *not* the input `\cite[\S2]{FFF}` uses.  It is
carried here because of what it shows about the small-cancellation route: the
embedding into a finitely presented Kazhdan group is available from an
independent and already-verified citation, and the normal-generation clause
is a bonus.  What it does not give is torsion-freeness.

Only the *conclusion* is recorded.  The theorem's hypothesis --- that the
source is finitely generated and recursively presented --- is not a field,
because every group this route feeds it is finitely presented and therefore
meets it outright; a structure asserting a hypothesis its every user
satisfies would be decoration.

Nothing inhabits this structure either; it is a second typed literature
input, not a discharge of the first. -/
structure NormalGeneratorEnvelope (U : Type) [Group U] where
  /-- The Chatterji--Kassabov envelope. -/
  Carrier : Type
  [groupCarrier : Group Carrier]
  [finitelyPresentedCarrier : Group.IsFinitelyPresented Carrier]
  /-- The envelope has property `(T)`. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Carrier
  /-- `U` sits inside the envelope. -/
  emb : U →* Carrier
  /-- The embedding is injective. -/
  emb_injective : Function.Injective emb
  /-- The prescribed element, chosen in advance inside `U`. -/
  normalGenerator : U
  /-- Chatterji--Kassabov choose it nontrivial, and so does this record. -/
  normalGenerator_ne_one : normalGenerator ≠ 1
  /-- The envelope is normally generated by the image of that element. -/
  normallyGenerated :
    Subgroup.normalClosure ({emb normalGenerator} : Set Carrier) = ⊤

instance normalGeneratorEnvelopeGroup {U : Type} [Group U]
    (N : NormalGeneratorEnvelope U) : Group N.Carrier :=
  N.groupCarrier

instance normalGeneratorEnvelopeFinitelyPresented {U : Type} [Group U]
    (N : NormalGeneratorEnvelope U) :
    Group.IsFinitelyPresented N.Carrier :=
  N.finitelyPresentedCarrier

/-- **Torsion-freeness is the only clause the Chatterji--Kassabov envelope
lacks.**  Given it, their theorem supplies a `KazhdanEnvelope` outright, and
therefore --- through `UniversalKazhdanGroup.ofInputs` --- the whole of
`KC.21`.

This is the sharpest available statement of what the small-cancellation
route is for.  Both routes deliver an embedding of `U` into a finitely
presented property-`(T)` group; only Osin's carries the torsion clause, and
that clause is the entire difference between an established citation in this
repository's research graph and an open one. -/
def NormalGeneratorEnvelope.toKazhdanEnvelope {U : Type} [Group U]
    (N : NormalGeneratorEnvelope U) (htf : IsPowerTorsionFree N.Carrier) :
    KazhdanEnvelope U where
  Carrier := N.Carrier
  groupCarrier := N.groupCarrier
  finitelyPresentedCarrier := N.finitelyPresentedCarrier
  torsionFree := htf
  kazhdan := N.kazhdan
  emb := N.emb
  emb_injective := N.emb_injective

end SmallCancellationEnvelope
end GroupApproximation
