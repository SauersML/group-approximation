import GroupApproximation.Sofic.BareDefectSource
import GroupApproximation.Sofic.BespokeRouterConstruction
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner

/-!
# The torsion-free finitely presented non-MF endpoint

This is the top of the tower: the final theorem of the program, stated in
its public `∃`-form and derived from the frozen lane beneath it.

The design rule is that exactly **one** load-bearing open leaf separates
the machine-checked chain from the headline.  That one is
`bespoke_routing_exists`: the assertion that the bespoke small-cancellation
router produces a term of `RoutingLemmaData` over the candidate partner
`Γ(3)`.  Everything below it — the slimmed keystone
`RoutingLemmaData.toBareRoutingData`, the corona machinery, and the non-MF
consequences — is already proved, and everything this file adds on top of
that keystone is proved here.

It is the only one in this layer.  The partner
`Kazhdan/TorsionFreeKazhdanPartner.lean` is fully certified: countable,
torsion-free, finitely presented and Kazhdan, with no open leaf left.

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
amenable base could not prove anything.  So this statement still owes a
Kazhdan base carrying a proper self-compression.

That obligation is sharp, not a formalization artifact, and in particular
the explicit source already in the library does not discharge it:
`isEmpty_bareDefectSourceData_multiplicative_int` proves that *no* slimmed
source has an infinite cyclic base, so `ConcreteCompressionSource.
integerSource` and every ascending HNN skeleton over `ℤ` are permanently
outside this interface.  The base has to be genuinely Kazhdan, and a
Kazhdan group admitting a proper self-compression is what the source half
of the open leaf below is for.

## Why the routing statement names a specific partner

`bespoke_routing_exists` is pinned to `gamma3Partner` rather than
universally quantified over `TorsionFreeKazhdanPartner`, and that is not
timidity: the universally quantified form is **false**.  A trivial group is
countable, torsion-free, finitely presented and Kazhdan, so it is a legal
partner, and `not_routingLemmaData_of_subsingleton_partner` below shows no
routing datum with a surviving protected element exists over it.  Any
parameterized version of the routing lemma therefore has to carry an
infiniteness or nontriviality hypothesis on the partner.
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

/-! ## The one load-bearing hypothesis -/

/-- **The bespoke routing lemma.**  There is a slimmed compression source
whose defect and protected element are routed, together with the Kazhdan
partner `Γ(3)`, onto a common quotient in the shape the keystone consumes.

This is the only open leaf between the machine-checked lane and the
theorems below.  It is not atomic: `nonempty_routingLemmaData_of_design`
below derives it from two separately tracked pieces —

* a `BareDefectSourceData`: a Kazhdan base with a proper self-compression,
  a centralizing root and a nontrivial marked commutator;
* a `BespokeRouter.RouterRelatorDesign` over it: the explicit avatar words
  and their piece ledger.

The word-level gates are a third obligation, but they are not visible in
this statement: `RouterRelatorDesign.routerData` reads them from
`GreendlingerFreeGate`, where they are the tracked leaves.  They are
deliberately not hypotheses of the theorems below — that would turn the
headline into a conditional statement, which is exactly what this
development exists to avoid. -/
theorem bespoke_routing_exists :
    ∃ (P : Type) (E : Type) (_ : Group P) (_ : Group E)
      (D : BareDefectSourceData P E),
      Nonempty
        (RoutingLemmaData E D.core.defectNormal D.s gamma3Partner.B) := by
  sorry

/-- **The routing lemma factors through the avatar construction.**  A
slimmed source, an explicit relator design over it, and the design's
word-level conclusions together produce the routed datum.  This is proved
outright and is axiom-clean, so the shape of the remaining work is
machine-checked rather than asserted in prose: once a design is built and
its `RouterConclusions` supplied, `bespoke_routing_exists` closes by
applying this lemma.

`RouterConclusions` is a hypothesis rather than a call because it is what
`GreendlingerFreeGate.router_conclusions_of_metric` delivers, and that file
still has open leaves.  Keeping it a hypothesis is what stops those leaves
from tainting this statement invisibly -- a declaration that merely calls
an incomplete constant depends on `sorryAx` without Lean warning at the
call site, so only the axiom audit would have caught it. -/
theorem nonempty_routingLemmaData_of_design
    {P : Type} {E : Type} [Group P] [Group E]
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (hc : Des.RouterConclusions) :
    Nonempty (RoutingLemmaData E D.core.defectNormal D.s gamma3Partner.B) :=
  ⟨Des.routerData hc⟩

#print axioms nonempty_routingLemmaData_of_design

/-! ## The assembly -/

/-- The routing lemma, pushed through the slimmed keystone.  Property `(T)`
of the routed quotient enters here and only here, from the partner's `(T)`;
this step is complete. -/
theorem exists_bareRoutingData :
    ∃ (P : Type) (E : Type) (_ : Group P) (_ : Group E)
      (D : BareDefectSourceData P E), Nonempty (BareRoutingData D) := by
  obtain ⟨P, E, _, _, D, ⟨Rt⟩⟩ := bespoke_routing_exists
  exact ⟨P, E, inferInstance, inferInstance, D,
    ⟨Rt.toBareRoutingData D gamma3Partner.kazhdan⟩⟩

/-- **The Main Theorem.**  There is a countable, torsion-free, finitely
presented group that is not MF — neither in the literal
Carrión--Dadarlat--Eckhardt sense nor in the equivalent unitary-sequence
sense.

Countability is a binder rather than a conjunct because `IsCDEOperatorMF`
is only defined for countable groups: the predicate takes the instance, so
the statement cannot be phrased with it on the right of the `∃`. -/
theorem exists_torsionFree_finitelyPresented_not_MF :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsPowerTorsionFree Q ∧
      Group.IsFinitelyPresented Q ∧
      ¬ IsCDEOperatorMF Q ∧
      ¬ IsOperatorMF Q := by
  obtain ⟨P, E, _, _, D, ⟨R⟩⟩ := exists_bareRoutingData
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  exact ⟨R.Quotient, inferInstance, inferInstance, R.torsionFree,
    R.finitelyPresented, R.not_isCDEOperatorMF, R.not_isOperatorMF⟩

/-- **The Main Theorem with the full profile.**  The same group is also
two-generated, nontrivial, Kazhdan, and equal to its own MF radical, and
every nontrivial quotient of it fails to be MF as well. -/
theorem exists_twoGenerated_torsionFree_kazhdan_not_MF :
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
  obtain ⟨P, E, _, _, D, ⟨R⟩⟩ := exists_bareRoutingData
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  refine ⟨R.Quotient, inferInstance, inferInstance, R.isTwoGenerated,
    R.finitelyPresented, R.torsionFree, R.kazhdan, R.quotientNontrivial,
    R.cdeMFResidual_eq_top, R.not_isCDEOperatorMF, R.not_isOperatorMF, ?_⟩
  intro H _ _ _ f hf
  exact R.quotient_not_isCDEOperatorMF f hf

end TorsionFreeNonMFEndpoint
end GroupApproximation
