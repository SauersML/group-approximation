import GroupApproximation.Sofic.BespokeRouterConstruction

/-!
# The router's gate layer, with the classical inputs as hypotheses

`Sofic.BespokeRouterConstruction` derives every structural field of
`RoutingLemmaData` from a `RouterRelatorDesign` outright — `defect_top`,
`generates`, `route_surjective`, `partner_surjective`, finite presentation, and
the well-definedness of both maps — and takes the two word-combinatorial fields
as the single named hypothesis `RouterRelatorDesign.RouterConclusions`.

This module reduces that hypothesis as far as it honestly goes without the
classical small-cancellation theorems, and supplies the two bridges a word
design needs to build the landed structure's fields from the shapes the avatar
construction actually yields.  It imports nothing with open leaves, contains no
incomplete proof, and is root-importable.

## What the reduction does and does not do

`routerConclusions_of_greendlinger` reduces `RouterConclusions` to

* `GreendlingerConclusion relators` — the ½-form metric conclusion, and
* `IsPowerTorsionFree Routed` — torsion-freeness of the routed quotient.

The first reduction is **real work**: the protected-set half is *derived* from
the Greendlinger conclusion by
`SmallCancellationRouter.injOn_mk'_of_greendlinger`, which is proved, against
the design's own `protectedBall` field.  That is the same data-not-axiom idiom
`protected_injOn_of_gate` already uses upstream.

The second is **a pass-through, and is labelled as one**: torsion-freeness of a
`C'(λ)` presentation without proper powers is a second classical theorem, not a
corollary of the Greendlinger conclusion, so nothing here can weaken it.  Its
proof is the two-occurrence dichotomy — distinct rotations give a piece, equal
rotations make the relator a proper power — and it lives with the gate.  Taking
it as a hypothesis is therefore honest bookkeeping rather than a reduction, and
a caller should read `routerConclusions_of_greendlinger` as "the protected-set
half is discharged; the torsion half is still owed".

When both classical theorems land, the unconditional form is one call and no
signature here moves: `router_conclusions_of_metric` supplies
`RouterConclusions` directly from the design's fields, and these theorems
become corollaries of it rather than the other way round.

## The two bridges, from the avatar word design

Both from `notes/W3_AVATAR_WORD_DESIGN_2026-08-21.md`, and both let a word
design discharge a landed field from the *stronger* statement the explicit
family gives, without changing the root-imported structure:

* `metricSmallCancellation_mono` (§2).  The avatar family is designed at
  `C'(1/8)`, not `C'(1/6)`: at `λ ≤ 1/8`, read in the sharp form
  `|u| > (1 − 3λ)|r|`, the torsion descent's residual case is arithmetically
  empty.  The landed `metric` field is stated at `1/6`, and monotonicity in the
  constant is what turns the design's `C'(1/8)` proof into it.  Threading `λ`
  through the structure itself is a coordinated edit with the `λ`-general
  consumption point, not a unilateral one.
* `mem_relSubgroup_of_image` (§4).  Well-definedness is *literal membership* of
  the rewritten relator in the family, while the landed fields ask for
  membership in its normal closure.  This is the one-line bridge.
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

/-- **The reduction.**  The protected-set half of `RouterConclusions` is
derived from the ½-form Greendlinger conclusion for the design's own family,
through the proved engine and the design's `protectedBall` field; the torsion
half is passed through, because it is a second classical theorem and not a
consequence of the first.  See the module docstring. -/
theorem routerConclusions_of_greendlinger
    (hG : GreendlingerConclusion D.relators)
    (htf : IsPowerTorsionFree D.Routed) : D.RouterConclusions :=
  ⟨injOn_mk'_of_greendlinger hG
      ({1, FreeGroup.lift D.W D.protectedWord} : Set RouterFree)
      D.protectedBall_short,
    htf⟩

/-- The router's output from the two classical inputs. -/
noncomputable def routerData_of_greendlinger [N.Normal]
    (hG : GreendlingerConclusion D.relators)
    (htf : IsPowerTorsionFree D.Routed) : RoutingLemmaData E N s B :=
  D.routerData (D.routerConclusions_of_greendlinger hG htf)

/-- Whoever exhibits a design, the Greendlinger conclusion for its family, and
torsion-freeness of its quotient has discharged the frozen endpoint's single
hypothesis at that source, defect, protected element and partner. -/
theorem nonempty_routingLemmaData_of_greendlinger [N.Normal]
    (hG : GreendlingerConclusion D.relators)
    (htf : IsPowerTorsionFree D.Routed) :
    Nonempty (RoutingLemmaData E N s B) :=
  ⟨D.routerData_of_greendlinger hG htf⟩

end RouterRelatorDesign
end BespokeRouter
end GroupApproximation
