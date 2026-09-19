import GroupApproximation.Sofic.BareDefectSource
import GroupApproximation.Sofic.BespokeRouterConstruction
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner

/-!
# The torsion-free finitely presented non-MF endpoint

This is the top of the tower: the final theorem of the program, stated in
its public `∃`-form and derived from the frozen lane beneath it.

Every declaration here is proved.  The design rule is that exactly **one**
explicit hypothesis, `BespokeRoutingLemma`, separates the machine-checked
chain from the headline: the assertion that the bespoke small-cancellation
router produces a term of `RoutingLemmaData` over the candidate partner
`Γ(3)`.  Everything below it — the slimmed keystone
`RoutingLemmaData.toBareRoutingData`, the corona machinery, and the non-MF
consequences — is already proved, and everything this file adds on top of
that keystone is proved here.

Carrying the routing lemma as a named `Prop` rather than as an incomplete
proof is what lets this file live on `main`: the module is complete, its
import closure is complete, and the one thing still owed is visible in the
type of every theorem that uses it.  The library uses the same idiom for
`GreendlingerGate`, `TorsionFreeGate` and `RouterConclusions`.  The day the
router instantiates, `BespokeRoutingLemma` becomes a theorem and the
unconditional forms are one-line corollaries.

The two headline theorems are named `..._of_routing` for that reason.  A
conditional result with an unconditional-sounding name is the one mistake
this development can least afford, so the bare names are reserved for the
day the hypothesis is discharged.

The partner is not a second obligation:
`Kazhdan/TorsionFreeKazhdanPartner.lean` is fully certified — countable,
torsion-free, finitely presented and Kazhdan, with nothing left open.

## What the source datum still owes

The existential ranges over `BareDefectSourceData`, the slimmed source of
`Sofic/BareDefectSource.lean`, not over `FournierFacioDefectData`.  That
removes the embedded infinite simple factor — `simpleSubgroup`, its
simplicity instance, and the two membership fields — which a consumer
trace showed no endpoint consequence reads.

It does **not** remove property `(T)` of the base `P`.  That field is
load-bearing: the marked-root capture extracts a symmetric generating pair
with a spectral gap from it, and the partner's `(T)` does not substitute.
The mathematics agrees — an ascending HNN extension over `ℤ` is
Baumslag--Solitar, hence amenable, hence MF, so a compression core over an
amenable base could not prove anything.  So the hypothesis still owes a
Kazhdan base carrying a proper self-compression.

That obligation is sharp, not a formalization artifact, and in particular
the explicit source already in the library does not discharge it:
`isEmpty_bareDefectSourceData_multiplicative_int` proves that *no* slimmed
source has an infinite cyclic base, so `ConcreteCompressionSource.
integerSource` and every ascending HNN skeleton over `ℤ` are permanently
outside this interface.  The base has to be genuinely Kazhdan, and a
Kazhdan group admitting a proper self-compression is what the source half
of the hypothesis is for.

## Why the routing statement names a specific partner

`BespokeRoutingLemma` is pinned to `gamma3Partner` rather than universally
quantified over `TorsionFreeKazhdanPartner`, and that is not timidity: the
universally quantified form is **false**.  A trivial group is countable,
torsion-free, finitely presented and Kazhdan, so it is a legal partner, and
`not_routingLemmaData_of_subsingleton_partner` below shows no routing datum
with a surviving protected element exists over it.  Any parameterized
version of the routing lemma therefore has to carry an infiniteness or
nontriviality hypothesis on the partner.
-/

namespace GroupApproximation
namespace TorsionFreeNonMFEndpoint

open SmallCancellationRouter CongruenceSubgroup

/-! ## The partner may not be arbitrary -/

/-- **A subsingleton partner admits no routing datum.**  The partner map is
onto, so a trivial partner collapses the routed quotient, and then the
protected element cannot survive.  This is the reason the routing statement
below names its partner instead of quantifying over all of them. -/
theorem not_routingLemmaData_of_subsingleton_partner
    {E : Type} [Group E] {N : Subgroup E} [N.Normal] {s : E} (hs : s ≠ 1)
    {B : Type} [Group B] [Subsingleton B]
    (R : RoutingLemmaData E N s B) : False := by
  letI : Group R.Quotient := R.groupQuotient
  apply hs
  apply R.protected_injOn (Set.mem_insert_of_mem _ rfl) (Set.mem_insert _ _)
  obtain ⟨a, ha⟩ := R.partner_surjective (R.route s)
  obtain ⟨b, hb⟩ := R.partner_surjective (R.route 1)
  rw [← ha, ← hb, Subsingleton.elim a b]

/-! ## The one hypothesis -/

/-- **The bespoke routing lemma, as a named proposition.**  There is a
slimmed compression source whose defect and protected element are routed,
together with the Kazhdan partner `Γ(3)`, onto a common quotient in the
shape the keystone consumes.

This is the whole remaining content of the program at this layer, and it
decomposes into three separately tracked obligations —

* a `BareDefectSourceData`: a Kazhdan base with a proper self-compression,
  a centralizing root and a nontrivial marked commutator;
* a relator design over it, from `Sofic/BespokeRouterConstruction.lean`:
  the explicit words and their piece ledger;
* that design's word-level conclusions, which
  `GreendlingerFreeGate.router_conclusions_of_metric` delivers.

`nonempty_routingLemmaData_of_design` below states the composition of the
first two, so that the shape of the remaining work is machine-checked
rather than asserted here in prose. -/
def BespokeRoutingLemma : Prop :=
  ∃ (P : Type) (E : Type) (_ : Group P) (_ : Group E)
    (D : BareDefectSourceData P E),
    Nonempty (RoutingLemmaData E D.core.defectNormal D.s gamma3Partner.B)

/-- **The routing lemma factors through the router construction.**  A
slimmed source and an explicit relator design over it, together with that
design's word-level conclusions, produce the routed datum.  Once a design
is built and its `RouterConclusions` supplied, `BespokeRoutingLemma`
follows by applying this lemma.

`RouterConclusions` is taken as a hypothesis rather than called, and that
is a deliberate containment choice.  It is what
`GreendlingerFreeGate.router_conclusions_of_metric` delivers, via
`Sofic/BespokeRouterGateAssembly.lean`; that gate is still incomplete, and
a declaration which merely calls an incomplete constant inherits the
incompleteness axiom without Lean warning at the call site, so only the
kernel audit would see it.  Keeping it a hypothesis is what keeps this
file, and the root import closure it joins, clean.  When the gate closes,
this becomes a call to `RouterRelatorDesign.routerDataOfDesign` and the
hypothesis disappears. -/
theorem nonempty_routingLemmaData_of_design
    {P : Type} {E : Type} [Group P] [Group E]
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (hc : Des.RouterConclusions) :
    Nonempty (RoutingLemmaData E D.core.defectNormal D.s gamma3Partner.B) :=
  ⟨Des.routerData hc⟩

/-! ## The assembly -/

/-- The routing lemma, pushed through the slimmed keystone.  Property `(T)`
of the routed quotient enters here and only here, from the partner's `(T)`;
this step is complete. -/
theorem exists_bareRoutingData (hroute : BespokeRoutingLemma) :
    ∃ (P : Type) (E : Type) (_ : Group P) (_ : Group E)
      (D : BareDefectSourceData P E), Nonempty (BareRoutingData D) := by
  obtain ⟨P, E, _, _, D, ⟨Rt⟩⟩ := hroute
  exact ⟨P, E, inferInstance, inferInstance, D,
    ⟨Rt.toBareRoutingData D gamma3Partner.kazhdan⟩⟩

/-- **The Main Theorem, modulo the routing lemma.**  Given the routing
lemma there is a countable, torsion-free, finitely presented group that is
not MF — neither in the literal Carrión--Dadarlat--Eckhardt sense nor in
the equivalent unitary-sequence sense.

Countability is a binder rather than a conjunct because `IsCDEOperatorMF`
is only defined for countable groups: the predicate takes the instance, so
the statement cannot be phrased with it on the right of the `∃`. -/
theorem exists_torsionFree_finitelyPresented_not_MF_of_routing
    (hroute : BespokeRoutingLemma) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsPowerTorsionFree Q ∧
      Group.IsFinitelyPresented Q ∧
      ¬ IsCDEOperatorMF Q ∧
      ¬ IsOperatorMF Q := by
  obtain ⟨P, E, _, _, D, ⟨R⟩⟩ := exists_bareRoutingData hroute
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  exact ⟨R.Quotient, inferInstance, inferInstance, R.torsionFree,
    R.finitelyPresented, R.not_isCDEOperatorMF, R.not_isOperatorMF⟩

/-- **The Main Theorem with the full profile, modulo the routing lemma.**
The same group is also two-generated, nontrivial, Kazhdan, and equal to its
own MF radical, and every nontrivial quotient of it fails to be MF. -/
theorem exists_twoGenerated_torsionFree_kazhdan_not_MF_of_routing
    (hroute : BespokeRoutingLemma) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsTwoGenerated Q ∧
      Group.IsFinitelyPresented Q ∧
      IsPowerTorsionFree Q ∧
      HasKazhdanPropertyT.{0, 0} Q ∧
      Nontrivial Q ∧
      cdeMFResidual Q = ⊤ ∧
      ¬ IsCDEOperatorMF Q ∧
      ¬ IsOperatorMF Q ∧
      ∀ (H : Type) (_ : Group H) (_ : Countable H) (_ : Nontrivial H)
        (f : Q →* H),
        Function.Surjective f → ¬ IsCDEOperatorMF H := by
  obtain ⟨P, E, _, _, D, ⟨R⟩⟩ := exists_bareRoutingData hroute
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  refine ⟨R.Quotient, inferInstance, inferInstance, R.isTwoGenerated,
    R.finitelyPresented, R.torsionFree, R.kazhdan, R.quotientNontrivial,
    R.cdeMFResidual_eq_top, R.not_isCDEOperatorMF, R.not_isOperatorMF, ?_⟩
  intro H _ _ _ f hf
  exact R.quotient_not_isCDEOperatorMF f hf

end TorsionFreeNonMFEndpoint
end GroupApproximation
