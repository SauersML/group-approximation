import GroupApproximation.Sofic.BespokeRouterConstruction
import GroupApproximation.Sofic.GreendlingerFreeGate

/-!
# The router's gate layer: discharging `RouterConclusions`

`Sofic.BespokeRouterConstruction` derives every structural field of
`RoutingLemmaData` from a `RouterRelatorDesign` outright — `defect_top`,
`generates`, `route_surjective`, `partner_surjective`, finite presentation, and
the well-definedness of both maps — and takes the two word-combinatorial fields
as the single named hypothesis `RouterRelatorDesign.RouterConclusions`.  That
hypothesis is verbatim the conclusion of
`GreendlingerFreeGate.router_conclusions_of_metric` at the design's data, and
the design's own fields are verbatim its hypothesis list.

This module is the one line that fits them together, plus the two small helpers
a word design needs to produce the landed structure's fields from the shapes
the avatar construction actually yields.  It adds no scaffolding of its own:
everything else lives in the landed module, which it imports.

**This module must not be root-imported until `Sofic.GreendlingerFreeGate` is
free of open leaves.**  It is the only module in the router lane that imports
the gate, and that is the point: a module may be root-imported only if its
whole transitive import closure is clean.  Keeping the import here rather than
in the construction leaves `Sofic.BespokeRouterConstruction` — which *is*
root-imported — clean, so the shared build of the default target passes.

**To an orphan sweep: this module is an intentional orphan — do not repair it
by adding `import GroupApproximation.Sofic.BespokeRouterGateAssembly` to
`GroupApproximation.lean`.**  Doing so pulls the gate's open leaves into the
root's transitive closure and reddens the default target for every lane; that
breakage has already happened once today, from exactly this shape one module
further in.  The module leaves orphan status the same day the leaves close,
and not before.

Nothing warns at the call sites below: a declaration built from an open leaf
inherits its axiom footprint silently, with no message at its own declaration,
so the axiom probe in `scripts/Audit.lean` is the gate of record for everything
here.  When the two leaves close, everything becomes unconditional and this
module can move to the root with no signature changing.

## The two helpers, and why they are here

Both come from `notes/W3_AVATAR_WORD_DESIGN_2026-08-21.md`, and both let a word
design discharge a landed field from the *stronger* statement the explicit
family gives, without changing the landed structure:

* `metricSmallCancellation_mono` (§2).  The avatar family is designed at
  `C'(1/8)`, not `C'(1/6)`: at `λ ≤ 1/8`, read in the sharp form
  `|u| > (1 − 3λ)|r|`, the torsion descent's residual case is arithmetically
  empty.  The landed structure's `metric` field is stated at `1/6`, which is
  what the consumption point currently asks for, and monotonicity in the
  constant is what turns the design's `C'(1/8)` proof into it.  When a
  `λ`-general consumption point lands, the landed structure should gain a `lam`
  parameter — a one-field change to a root-imported module, so it is scheduled
  rather than done here.
* `mem_relSubgroup_of_image` (§4).  Well-definedness is *literal membership* of
  the rewritten relator in the family — `subset_normalClosure`-level, no
  combinatorics — while the landed fields ask for membership in its normal
  closure.  This is the one-line bridge.
-/

namespace GroupApproximation
namespace BespokeRouter

open SmallCancellationRouter

/-- **The metric condition is monotone in its constant.**  A family designed at
`C'(1/8)` satisfies the `C'(1/6)` that `RouterRelatorDesign.metric` asks for. -/
theorem metricSmallCancellation_mono {R : Set (List (Fin 2 × Bool))}
    {lam lam' : ℚ} (h : lam ≤ lam') (hm : MetricSmallCancellation R lam) :
    MetricSmallCancellation R lam' := by
  intro p hp w hw hpre
  have h1 := hm p hp w hw hpre
  have h2 : lam * (w.length : ℚ) ≤ lam' * (w.length : ℚ) :=
    mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _)
  linarith

/-- **Literal membership suffices for well-definedness.**  A rewritten relator
that *is* one of the relators lies in the subgroup they present, which is what
`srcRel_rewrite` and `parRel_rewrite` ask for. -/
theorem mem_relSubgroup_of_image {R : Set (List (Fin 2 × Bool))}
    {g : FreeGroup (Fin 2)} (hg : g ∈ FreeGroup.mk '' R) : g ∈ relSubgroup R :=
  Subgroup.subset_normalClosure hg

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
`BespokeRouterConstruction` carries is discharged by one call.  This is the
only declaration in the router lane that touches the open leaves. -/
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
