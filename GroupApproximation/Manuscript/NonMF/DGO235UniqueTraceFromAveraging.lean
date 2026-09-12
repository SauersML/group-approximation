import GroupApproximation.Analysis.PowersAveragingUniqueTrace
import GroupApproximation.Manuscript.NonMF.OsinTheorem12NonDegenerate

/-!
# Dahmani--Guirardel--Osin, Theorem 2.35, on a single analytic hypothesis

`Manuscript/NonMF/OsinTheorem12NonDegenerate` proves Osin's Theorem 1.2 and
reduces `DGOTheorem235Printed` to `SimpleUniqueTraceAtHypEmbedded`, the citation
at its own hypotheses.  This module reduces *that* to one statement:

> the Powers averaging estimate holds for `G`.

## Why one hypothesis and not three

`Manuscript/NonMF/DGOTheorem235Slice` opens DGO's own proof and lands on three
classical C⋆ citations — Powers, Akemann--Lee, Breuillard--Kalantar--Kennedy--
Ozawa — together with a group-theoretic residue.  The third of those,
`BKKOUniqueTraceOfCStarSimple`, is needed only because C⋆-simplicity by itself
does not visibly give uniqueness of the trace: DGO's Lemma 8.15 as printed
concludes simplicity alone.

Powers *averaging* is stronger than simplicity, and it gives both conclusions.
`Analysis/PowersAveragingUniqueTrace` proves the trace half;
`Analysis/PowersAveraging` had already proved the simplicity half.  So a route
that carries the averaging estimate rather than its consequence never has to
cite BKKO at all, and the two conclusions of DGO 2.35 come out together.

## What is proved here

* `hasUniqueTracialState_of_powersAveragingEstimate` and
  `simpleUniqueTrace_of_powersAveragingEstimate` — the two clauses of DGO 2.35
  from the estimate, at any group.
* `PowersAveragingAtHypEmbedded` — the estimate at exactly DGO's hypotheses.
* `dgoTheorem235Printed_of_powersAveraging` — the printed citation from that one
  Prop, through the *proved* Osin Theorem 1.2.

## The residual, stated exactly

What is left of `cor:regular-nonmf-algebra`'s appeal to DGO's Theorem 2.35 is

```text
∀ (G : Type) [Group G] [Countable G],
  (∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E) →
    HasTrivialFiniteRadical G →
      ∀ a : ReducedGroupCStar G, canonicalFaithfulTracialState G a = 0 →
        ∀ ε : ℝ, 0 < ε →
          ∃ (n : ℕ) (g : Fin n → G), 0 < n ∧
            ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
                reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i))‖ ≤ ε
```

and nothing else.  That is a single quantitative estimate about `ℓ²(G)`, with no
C⋆-algebra citation left anywhere in the chain.

## Manuscript status

Reduction step for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.ReducedGroupCStarTrace

/-! ## The two clauses of DGO 2.35, from the estimate -/

/-- **The unique-trace clause, from Powers averaging.**

The canonical trace is a tracial state, and
`tracialState_eq_canonical_of_powersAveragingEstimate` says every tracial state
equals it pointwise. -/
theorem hasUniqueTracialState_of_powersAveragingEstimate (G : Type) [Group G]
    (h : PowersAveragingEstimate G) : HasUniqueTracialState (ReducedGroupCStar G) := by
  refine ⟨(canonicalFaithfulTracialState G).toTracialState, fun σ x ↦ ?_⟩
  rw [FaithfulTracialState.coe_toTracialState]
  exact tracialState_eq_canonical_of_powersAveragingEstimate G h σ x

/-- **Both clauses of DGO's Theorem 2.35, from one estimate.**

Simplicity is `Analysis/PowersAveraging`'s component (D); the unique trace is
the theorem above.  No classical C⋆ citation is used. -/
theorem simpleUniqueTrace_of_powersAveragingEstimate (G : Type) [Group G]
    (h : PowersAveragingEstimate G) :
    IsSimpleCStar (ReducedGroupCStar G) ∧ HasUniqueTracialState (ReducedGroupCStar G) :=
  ⟨isSimpleCStar_of_powersAveragingEstimate G h,
    hasUniqueTracialState_of_powersAveragingEstimate G h⟩

/-! ## The single remaining hypothesis -/

/-- **The Powers averaging estimate at Dahmani--Guirardel--Osin's own
hypotheses**: a countable group with a non-degenerate hyperbolically embedded
subgroup and no nontrivial finite normal subgroup.

This is the entire residual of DGO's Theorem 2.35 as the manuscript uses it. -/
def PowersAveragingAtHypEmbedded : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    (∃ E : Subgroup G, GGT.IsNonDegenerate E ∧ GGT.IsHypEmbedded G E) →
      HasTrivialFiniteRadical G → PowersAveragingEstimate G

/-- **DGO's Theorem 2.35 at its own hypotheses, from the estimate.** -/
theorem simpleUniqueTraceAtHypEmbedded_of_powersAveraging
    (h : PowersAveragingAtHypEmbedded) : SimpleUniqueTraceAtHypEmbedded := by
  intro G instG instC hemb hrad
  letI := instG
  letI := instC
  exact simpleUniqueTrace_of_powersAveragingEstimate G (h G hemb hrad)

/-- **`DGOTheorem235Printed` rests on the averaging estimate alone.**

The bridge from DGO's hypotheses to the printed ones is
`dgoTheorem235Printed_of_hypEmbedded`, whose input is the *proved* Osin
Theorem 1.2. -/
theorem dgoTheorem235Printed_of_powersAveraging
    (h : PowersAveragingAtHypEmbedded) : DGOTheorem235Printed :=
  dgoTheorem235Printed_of_hypEmbedded
    (simpleUniqueTraceAtHypEmbedded_of_powersAveraging h)

/-- **The same reduction stated at acylindrical hyperbolicity**, which is the
hypothesis the printed corollary actually has in hand.  Weaker than
`PowersAveragingAtHypEmbedded` as a hypothesis — Osin's Theorem 1.2 turns one
into the other — and so the more convenient form for a future producer. -/
def PowersAveragingAtAcylindricallyHyperbolic : Prop :=
  ∀ (G : Type) [Group G] [Countable G] [IsAcylindricallyHyperbolic G],
    HasTrivialFiniteRadical G → PowersAveragingEstimate G

/-- **`DGOTheorem235Printed` from the acylindrically hyperbolic form.** -/
theorem dgoTheorem235Printed_of_powersAveraging_acylHyperbolic
    (h : PowersAveragingAtAcylindricallyHyperbolic) : DGOTheorem235Printed := by
  intro G instG instC instAH hrad
  letI := instG
  letI := instC
  letI := instAH
  exact simpleUniqueTrace_of_powersAveragingEstimate G (h G hrad)

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms hasUniqueTracialState_of_powersAveragingEstimate
#audit_axioms simpleUniqueTrace_of_powersAveragingEstimate
#audit_axioms simpleUniqueTraceAtHypEmbedded_of_powersAveraging
#audit_axioms dgoTheorem235Printed_of_powersAveraging
#audit_axioms dgoTheorem235Printed_of_powersAveraging_acylHyperbolic
