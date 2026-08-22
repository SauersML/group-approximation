import GroupApproximation.Sofic.TorsionFreeNonMFEndpoint
import GroupApproximation.Sofic.AvatarMetricCheck
import GroupApproximation.Sofic.FournierFacioUniversalGroup

/-!
# The finish line, assembled

`Sofic/TorsionFreeNonMFEndpoint.lean` states the headline theorems relative to
one named `Prop`, `BespokeRoutingLemma`.  Three other modules each discharge a
different part of what that `Prop` needs, and each does so relative to its own
named hypothesis.  This file is the composition: it walks the chain once, in
public, so that the remaining work is a list of *binders in a single signature*
rather than a paragraph of prose.

The chain, bottom to top:

* `Sofic/BareDefectSource.lean` -- `BareDefectSourceData P E`: a Kazhdan base
  with a proper self-compression, a centralizing root and a nontrivial marked
  commutator.  Nothing here builds one; it is a binder.
* `Sofic/BespokeRouterConstruction.lean` -- `RouterRelatorDesign`, over that
  source at the partner `Γ(3)`.  Every *structural* field of the routing datum
  is already derived from it; the two word-combinatorial fields are its
  `RouterConclusions` hypothesis.
* `Sofic/AvatarMetricCheck.lean` -- `AvatarMetricData`, the six word
  obligations on the relator family (`relators_long`, `runs_short`, `pinned`,
  `uniqueMark`, `metric_margin`, `protected_margin`), from which `C'(1/8)`, the
  no-block-power condition and the protected ball all follow.
* `Sofic/GreendlingerFreeGate.lean` -- `SharpGreendlingerGate (Fin 2)`, the
  word-combinatorial gate, carried as a `Prop` in the library's data-not-axiom
  style.

`bespokeRoutingLemma_of_components` takes exactly those, and nothing else, and
returns `BespokeRoutingLemma`.  Every step between is a named lemma, so the day
a component lands its binder disappears from all of them at once and no
statement changes shape.

## What this file does not add

No mathematics.  Every declaration is a composition of results that are already
proved in the modules above; the content is the *typing*, which is the part
prose gets wrong.  In particular the two facts most easily misstated are
machine-checked here rather than asserted:

* the `λ` arithmetic does not need restating -- `routerConclusions_of_check`
  already spends `metric_eighth` at `le_refl (1/8)`, and the design's stored
  `C'(1/6)` is never read backwards;
* the normality instance on `D.core.defectNormal` is found, not supplied:
  `KazhdanCompressionCore.defectNormal_normal` is registered, which is why
  `routerData`'s `[N.Normal]` binder never appears in any signature below.

## Open leaves

None of its own.  This module proves nothing unconditionally and asserts
nothing unconditionally: every theorem carries its components as explicit
binders, exactly as the endpoint file carries `BespokeRoutingLemma`.
-/

namespace GroupApproximation
namespace TorsionFreeAssembly

open SmallCancellationRouter CongruenceSubgroup

/-! ## 1.  The chain, component by component -/

section Components

variable {P E : Type} [Group P] [Group E]

/-- **Step one: the word-combinatorial fields.**  The metric check bundle and
the gate deliver both halves of `RouterConclusions` for a design whose relator
family is the checked one.

This is `AvatarMetricCheck.routerConclusions_of_check` specialized to a design
over a slimmed source at the partner `Γ(3)`, which is the only shape the
endpoint consumes. -/
theorem routerConclusions_of_components
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    Des.RouterConclusions :=
  AvatarMetricCheck.routerConclusions_of_check Des C hrel hgate

/-- **Step two: the routing datum.**  The design supplies every structural
field, step one supplies the two word-combinatorial ones.

The normality of `D.core.defectNormal`, which `RouterRelatorDesign.routerData`
requires, is discharged by instance search from
`KazhdanCompressionCore.defectNormal_normal`; it is deliberately not a
binder. -/
theorem nonempty_routingLemmaData_of_components
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    Nonempty (RoutingLemmaData E D.core.defectNormal D.s gamma3Partner.B) :=
  TorsionFreeNonMFEndpoint.nonempty_routingLemmaData_of_design D Des
    (routerConclusions_of_components D Des C hrel hgate)

/-- **Step three: the endpoint's single hypothesis.**

This is the theorem the whole file exists for: `BespokeRoutingLemma` from
*exactly* the four remaining components -- a slimmed source, a relator design
over it at `Γ(3)`, a metric check bundle matching that design's family, and the
sharp Greendlinger gate.  Nothing else is owed. -/
theorem bespokeRoutingLemma_of_components
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    TorsionFreeNonMFEndpoint.BespokeRoutingLemma := by
  show ∃ (P₀ : Type) (E₀ : Type) (_ : Group P₀) (_ : Group E₀)
      (D₀ : BareDefectSourceData P₀ E₀),
      Nonempty (RoutingLemmaData E₀ D₀.core.defectNormal D₀.s gamma3Partner.B)
  exact ⟨P, E, inferInstance, inferInstance, D,
    nonempty_routingLemmaData_of_components D Des C hrel hgate⟩

/-- **Step four: through the slimmed keystone.**  Property `(T)` of the routed
quotient enters at this step and only at this step, from the partner's `(T)`;
it is already proved, so no component pays for it. -/
theorem exists_bareRoutingData_of_components
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    ∃ (P' : Type) (E' : Type) (_ : Group P') (_ : Group E')
      (D' : BareDefectSourceData P' E'), Nonempty (BareRoutingData D') :=
  TorsionFreeNonMFEndpoint.exists_bareRoutingData
    (bespokeRoutingLemma_of_components D Des C hrel hgate)

/-! ## 2.  The headline theorems, with the components as the only binders -/

/-- **The Main Theorem, from the components.**  A countable, torsion-free,
finitely presented group that is not MF -- neither in the literal
Carrión--Dadarlat--Eckhardt sense nor in the equivalent unitary-sequence
sense. -/
theorem exists_torsionFree_finitelyPresented_not_MF_of_components
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
      IsPowerTorsionFree Q ∧
      Group.IsFinitelyPresented Q ∧
      ¬ IsCDEOperatorMF Q ∧
      ¬ IsOperatorMF Q :=
  TorsionFreeNonMFEndpoint.exists_torsionFree_finitelyPresented_not_MF_of_routing
    (bespokeRoutingLemma_of_components D Des C hrel hgate)

/-- **The Main Theorem with the full profile, from the components.**  The same
group is also two-generated, nontrivial, Kazhdan, and equal to its own MF
radical, and every nontrivial quotient of it fails to be MF.

This is the finish line.  When the four binders are discharged the theorem is
unconditional and the program is over. -/
theorem exists_twoGenerated_torsionFree_kazhdan_not_MF_of_components
    (D : BareDefectSourceData P E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
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
        Function.Surjective f → ¬ IsCDEOperatorMF H :=
  TorsionFreeNonMFEndpoint.exists_twoGenerated_torsionFree_kazhdan_not_MF_of_routing
    (bespokeRoutingLemma_of_components D Des C hrel hgate)

end Components

/-! ## 3.  Entering the chain at `KC.21`

The source binder is the one a sibling module is building from the universal
Kazhdan group of `Sofic/FournierFacioUniversalGroup.lean`, under the name
`bareDefectSourceData_of_universalKazhdan`.  That module does not exist yet, so
its conclusion appears here as a hypothesis rather than as a call.

`bespokeRoutingLemma_of_universalKazhdan` is the shape to check the sibling
against: it is `bespokeRoutingLemma_of_components` with the base `P`
instantiated at `U.Carrier` and *nothing else changed*.  If the sibling's
lemma produces a source over that carrier, this theorem accepts it as written. -/

section UniversalKazhdan

/-- **The chain entered at `KC.21`.**  With the Kazhdan base taken to be the
carrier of a universal Kazhdan group, the routing lemma follows from the same
four components as before.

The `D` binder is what `bareDefectSourceData_of_universalKazhdan U` is expected
to supply. -/
theorem bespokeRoutingLemma_of_universalKazhdan {E : Type} [Group E]
    (U : FournierFacioUniversal.UniversalKazhdanGroup)
    (D : BareDefectSourceData U.Carrier E)
    (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
      gamma3Partner.B)
    (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : Des.relators = C.relators)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    TorsionFreeNonMFEndpoint.BespokeRoutingLemma :=
  bespokeRoutingLemma_of_components D Des C hrel hgate

/-- **The router half, as one named proposition.**  Over the carrier of a
universal Kazhdan group there is a slimmed source, a relator design over it at
the partner `Γ(3)`, and a metric check bundle matching that design's family.

The three are bundled rather than left as separate binders for a reason that is
not stylistic: a `RouterRelatorDesign` is *indexed by* its source, so a design
binder cannot be stated before a source binder is chosen.  Splitting them would
force a hypothesis quantified over every source, which is strictly stronger
than anything anyone intends to prove.  `AvatarMetricData` is genuinely
independent of the source and is kept as its own binder in section 1; it is
folded in here only because the match `Des.relators = C.relators` names the
design. -/
def CheckedDesignOverUniversal : Prop :=
  ∀ U : FournierFacioUniversal.UniversalKazhdanGroup,
    ∃ (E : Type) (_ : Group E) (D : BareDefectSourceData U.Carrier E)
      (Des : BespokeRouter.RouterRelatorDesign E D.core.defectNormal D.s
        gamma3Partner.B)
      (C : AvatarMetricCheck.AvatarMetricData), Des.relators = C.relators

/-- **The routing lemma from the `KC.21` input.**  Two binders: the router half
over the universal group, and the gate. -/
theorem bespokeRoutingLemma_of_universalKazhdan_nonempty
    (hU : Nonempty FournierFacioUniversal.UniversalKazhdanGroup)
    (hrouter : CheckedDesignOverUniversal)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    TorsionFreeNonMFEndpoint.BespokeRoutingLemma := by
  obtain ⟨U⟩ := hU
  obtain ⟨E, _, D, Des, C, hrel⟩ := hrouter U
  exact bespokeRoutingLemma_of_components D Des C hrel hgate

/-- **The finish line, entered at `KC.21`.**  The full profile of the headline
group, from three binders: the existence of a universal Kazhdan group, the
router half over it, and the sharp Greendlinger gate. -/
theorem exists_twoGenerated_torsionFree_kazhdan_not_MF_of_universalKazhdan
    (hU : Nonempty FournierFacioUniversal.UniversalKazhdanGroup)
    (hrouter : CheckedDesignOverUniversal)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
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
        Function.Surjective f → ¬ IsCDEOperatorMF H :=
  TorsionFreeNonMFEndpoint.exists_twoGenerated_torsionFree_kazhdan_not_MF_of_routing
    (bespokeRoutingLemma_of_universalKazhdan_nonempty hU hrouter hgate)

end UniversalKazhdan

end TorsionFreeAssembly
end GroupApproximation
