import GroupApproximation.Sofic.BespokeRouterConstruction
import GroupApproximation.Sofic.GreendlingerFreeGate

/-!
# The router's gate layer: `RouterConclusions` from the sharp gate

`Sofic.BespokeRouterConstruction` derives every structural field of
`RoutingLemmaData` from a `RouterRelatorDesign` outright — `defect_top`,
`generates`, `route_surjective`, `partner_surjective`, finite presentation, and
the well-definedness of both maps — and takes the two word-combinatorial fields
as the single named hypothesis `RouterRelatorDesign.RouterConclusions`.

This module discharges that hypothesis from
`GreendlingerFreeGate.router_conclusions_of_sharpGate`, whose only assumption
is the `Prop` `SharpGreendlingerGate (Fin 2)`.  Both files are free of open
leaves, so this one is too: `SharpGreendlingerGate` is carried as an explicit
hypothesis in the library's data-not-axiom style, never as an axiom, and every
declaration here is axiom-clean.  When the gate is proved, each signature loses
its first hypothesis and nothing else changes.

## The `λ` arithmetic, which does not go the way it looks

`router_conclusions_of_sharpGate` asks for `hlam8 : lam ≤ 1/8` together with
`MetricSmallCancellation R lam`.  The landed `RouterRelatorDesign.metric` field
is stated at `1/6`, and **a `C'(1/6)` field cannot supply that call**:
monotonicity in the constant runs `C'(1/8) → C'(1/6)`, never the reverse, and
`1/6 ≤ 1/8` is false.  So the sharper metric is taken here as an explicit
hypothesis alongside the gate, rather than read off the design.

That makes `metricSmallCancellation_mono` more useful, not less.  A word design
proves `C'(1/8)` once; monotonicity turns that single proof into the landed
`metric` field at `1/6`, and the same `C'(1/8)` proof is passed to the gate
call here.  The alternative — parameterizing the landed structure's `metric`
field by `λ` — removes the extra hypothesis, but it edits a root-imported
structure and is a coordinated change rather than a unilateral one.

## The two bridges, from the avatar word design

Both from `notes/W3_AVATAR_WORD_DESIGN_2026-08-21.md`, and both let a word
design discharge a landed field from the *stronger* statement the explicit
family gives:

* `metricSmallCancellation_mono` (§2).  The avatar family is designed at
  `C'(1/8)`, because at `λ ≤ 1/8` the sharp reading `|u| > (1 − 3λ)|r|` is what
  the torsion descent consumes.  See above for why this is now load-bearing in
  both directions.
* `mem_relSubgroup_of_image` (§4).  Well-definedness is *literal membership* of
  the rewritten relator in the family, while the landed fields ask for
  membership in its normal closure.  This is the one-line bridge.
-/

namespace GroupApproximation
namespace BespokeRouter

open SmallCancellationRouter

/-- **The metric condition is monotone in its constant.**  A family designed at
`C'(1/8)` satisfies the `C'(1/6)` that `RouterRelatorDesign.metric` asks for,
so one `C'(1/8)` proof serves both the landed field and the gate call. -/
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

/-- **Direct concrete consumption.**  A router design does not need the
universally quantified `SharpGreendlingerGate`: it is enough to prove the
sharp conclusion for this design's own relator family.  This is the endpoint
used by the literal construction, so no global small-cancellation theorem is
left as a caller premise. -/
theorem routerConclusions_of_sharp
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hsharp : GreendlingerConclusionSharp D.relators lam)
    (hmetric : MetricSmallCancellation D.relators lam) :
    D.RouterConclusions := by
  constructor
  · exact injOn_mk'_of_greendlinger
      (GreendlingerFreeGate.greendlingerConclusion_of_sharp (by linarith) hsharp)
      ({1, FreeGroup.lift D.W D.protectedWord} : Set RouterFree)
      D.protectedBall_short
  · exact TorsionDescent.isPowerTorsionFree_of_sharp hlam8 hsharp hmetric
      D.relators_noProperPower

/-- The routed quotient from a sharp conclusion proved specifically for this
finite design. -/
noncomputable def routerData_of_sharp [N.Normal]
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hsharp : GreendlingerConclusionSharp D.relators lam)
    (hmetric : MetricSmallCancellation D.relators lam) :
    RoutingLemmaData E N s B :=
  D.routerData (D.routerConclusions_of_sharp hlam8 hsharp hmetric)

/-- Existential wrapper for the concrete sharp-consumption path. -/
theorem nonempty_routingLemmaData_of_sharp [N.Normal]
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hsharp : GreendlingerConclusionSharp D.relators lam)
    (hmetric : MetricSmallCancellation D.relators lam) :
    Nonempty (RoutingLemmaData E N s B) :=
  ⟨D.routerData_of_sharp hlam8 hsharp hmetric⟩

/-- The router's word-level no-proper-power condition is the gate file's, on
the nose: both unfold to `∀ r ∈ R, ¬ PeriodicOverlap.IsProperPower r`. -/
theorem noProperPower_eq_gate :
    NoProperPower D.relators ↔
      GreendlingerFreeGate.NoProperPower D.relators :=
  Iff.rfl

/-- **The consumption point.**  Both word-combinatorial fields of the interface
from one gate hypothesis, at the family's own constant.

The design supplies cyclic reducedness, the no-proper-power condition and the
protected ball; the caller supplies the gate and the `C'(λ)` proof at
`λ ≤ 1/8`, for the reason in the module docstring. -/
theorem routerConclusions_of_sharpGate
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    D.RouterConclusions :=
  GreendlingerFreeGate.router_conclusions_of_sharpGate hgate hlam8
    D.relators_cyclicallyReduced hmetric D.relators_noProperPower
    ({1, FreeGroup.lift D.W D.protectedWord} : Set RouterFree)
    D.protectedBall_short

/-- The router's output from the gate. -/
noncomputable def routerData_of_sharpGate [N.Normal]
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    RoutingLemmaData E N s B :=
  D.routerData (D.routerConclusions_of_sharpGate hgate hlam8 hmetric)

/-- Whoever exhibits a design whose family is `C'(1/8)` has discharged the
frozen endpoint's single hypothesis at that source, defect, protected element
and partner — modulo the gate, and nothing else. -/
theorem nonempty_routingLemmaData_of_sharpGate [N.Normal]
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2))
    {lam : ℚ} (hlam8 : lam ≤ 1 / 8)
    (hmetric : MetricSmallCancellation D.relators lam) :
    Nonempty (RoutingLemmaData E N s B) :=
  ⟨D.routerData_of_sharpGate hgate hlam8 hmetric⟩

end RouterRelatorDesign
end BespokeRouter
end GroupApproximation
