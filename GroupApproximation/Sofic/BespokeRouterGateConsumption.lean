import GroupApproximation.Sofic.BespokeRouterConstruction
import GroupApproximation.Sofic.GreendlingerFreeGate

/-!
# Discharging the router's word-combinatorial hypothesis from the free gate

`Sofic.BespokeRouterConstruction` derives every structural field of
`RoutingLemmaData` from a `RouterRelatorDesign` outright, and takes the two
word-combinatorial fields — injectivity on the protected pair and
torsion-freeness of the quotient — as the single hypothesis
`RouterRelatorDesign.RouterConclusions`.  That hypothesis is verbatim the
conclusion of `GreendlingerFreeGate.router_conclusions_of_metric`, and the
design's fields are verbatim its hypothesis list.  This file is the one line
that puts the two together, plus the resulting hypothesis-free router.

**This module must not be root-imported until `Sofic.GreendlingerFreeGate` is
free of open leaves.**  It is the only module in the router lane that imports
the gate, and that is the point: a module may be root-imported only if its
whole transitive import closure is clean, and the gate file still carries
`greendlingerConclusion_of_metric` and
`isPowerTorsionFree_of_metricSmallCancellation` as open leaves.  Keeping the
import here rather than in the construction leaves
`Sofic.BespokeRouterConstruction` — which *is* root-imported — clean, so the
shared build of the default target passes.

Nothing warns at the call sites below.  A declaration built from an open leaf
inherits its axiom footprint silently, with no message at its own declaration,
so the axiom probe in `scripts/Audit.lean` is the gate of record for everything
in this file.  When the two leaves close, everything here becomes
unconditional and the module can move to the root with no signature changing.
-/

namespace GroupApproximation
namespace BespokeRouter
namespace RouterRelatorDesign

variable {E : Type} [Group E] {N : Subgroup E} {s : E} {B : Type} [Group B]
    (D : RouterRelatorDesign E N s B)

/-- The router's word-level no-proper-power condition is the gate file's, on
the nose: both unfold to `∀ r ∈ R, ¬ PeriodicOverlap.IsProperPower r`. -/
theorem noProperPower_eq_gate :
    NoProperPower D.relators ↔
      GreendlingerFreeGate.NoProperPower D.relators :=
  Iff.rfl

/-- **The consumption point.**  The design's own fields are exactly the
hypothesis list of the free-group gate's router conclusion, so the hypothesis
`BespokeRouterConstruction` carries is discharged by one call. -/
theorem routerConclusions : D.RouterConclusions :=
  GreendlingerFreeGate.router_conclusions_of_metric
    D.relators_cyclicallyReduced D.metric D.relators_noProperPower _
    D.protectedBall_short

/-- **The router, with no hypothesis left.**  Every field of the frozen
interface from a `RouterRelatorDesign` alone. -/
noncomputable def routerDataOfDesign [N.Normal] :
    SmallCancellationRouter.RoutingLemmaData E N s B :=
  D.routerData D.routerConclusions

/-- Whoever exhibits a design has discharged the frozen endpoint's single
hypothesis at that source, defect, protected element and partner. -/
theorem nonempty_routingLemmaData [N.Normal]
    (h : Nonempty (RouterRelatorDesign E N s B)) :
    Nonempty (SmallCancellationRouter.RoutingLemmaData E N s B) := by
  obtain ⟨D⟩ := h
  exact ⟨D.routerDataOfDesign⟩

end RouterRelatorDesign
end BespokeRouter
end GroupApproximation
