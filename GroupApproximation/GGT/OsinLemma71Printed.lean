import GroupApproximation.GGT.ElementaryOsinNormalClosed
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Manuscript.NonMF.HullPrintedInputs
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 7.1 in the printed case, discharged

`non_mf_groups_exist.tex`, `sec:torsion-free`, proof of `lem:saturation`:

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1].

`Manuscript/NonMF/HullPrintedInputs.lean` states that sentence's citation as the
closed proposition `TorsionFreePrinted.OsinLemma71Printed` and carries it as a
field of `HullPrintedInputs`.  This module **proves** it, so the field is no
longer an input: `osinLemma71Printed` is hypothesis-free and
`hullPrintedInputs_of_smallCancellation` builds the whole bundle out of Hull's
Theorem 7.1 alone.

## The two halves

Both were already theorems of this repository; what was missing was the
composition at the printed hypotheses, and the universe at which it is taken.

* **Algebraic.** `TorsionFree.isSNormal_of_torsionFree`
  (`Manuscript/NonMF/Saturation.lean`) is the printed sentence's own
  justification: a normal subgroup equals each of its twisted intersections
  (`twistedInter_eq_of_normal`), and over a torsion-free group a nontrivial
  subgroup contains an element of infinite order, so that intersection is
  infinite.  That is exactly Osin's `s`-normality, `HullSuitable.IsSNormal`.

* **Geometric.** `Elementary.osinNonElementary_of_torsionFree_normal_closed`
  (`GGT/ElementaryOsinNormalClosed.lean`) is Osin's Lemma 7.1 at Hull's Cayley
  graph for a normal `s`-normal subgroup of a torsion-free group, with both
  residuals of the `ElementaryBowditch` chain discharged
  (`ElementaryMorse.centralizerOrbitNearAxis_cayley` and
  `ElementaryMorse.independentOfNoCommonZpow_cayley`) and Bowditch's dichotomy
  replaced by `isLoxodromic_of_commute_of_orbitNearAxis`.  It is stated for
  `G : Type u`, which is the generality `OsinLemma71Printed.{u}` asks for;
  `Elementary.osinLemma71_closed` in the same file is the `Type 0` restriction
  and is not what the printed bundle needs.

Nothing here weakens the printed statement.  `HullGeneratingSet G` is the
printed acylindrical hyperbolicity data — `Γ(G,A)` hyperbolic, the translation
action acylindrical, `G` non-elementary on it — and the hypotheses on `N` are
the printed three and no others: `G` torsion-free, `N` normal, `N ≠ 1`.

## What is left for the lead

`GroupApproximation.lean` still has to import this module, and
`TorsionFreePrintedSentences.manuscriptSentence_saturationOsinNonElementary`
still takes `OsinLemma71Printed.{0}` as a binder that
`manuscriptSentence_saturationOsinClosed` below makes unnecessary.  Lanes do not
edit the root.
-/

namespace GroupApproximation
namespace GGT
namespace OsinPrinted

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

universe u

/-! ## The printed case of Osin's Lemma 7.1 -/

/-- **Osin, Lemma 7.1, in the case `lem:saturation` uses it**, in usable form.

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1].

The printed hypotheses and no others: `G` torsion-free, `N` normal, `N ≠ ⊥`.
`s`-normality — the hypothesis Osin's lemma carries in general — is derived from
them by `isSNormal_of_torsionFree`, which is the printed sentence's own
justification, and the geometric lemma is then
`Elementary.osinNonElementary_of_torsionFree_normal_closed`. -/
theorem actsNonElementarily_of_torsionFree_of_ne_bot {G : Type u} [Group G]
    (A : HullGeneratingSet G) (htf : IsPowerTorsionFree G) (N : Subgroup G)
    [N.Normal] (hN : N ≠ ⊥) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  Elementary.osinNonElementary_of_torsionFree_normal_closed A htf N
    (isSNormal_of_torsionFree htf N hN)

/-- **`OsinLemma71Printed` is a theorem.**

The second of the two citations `sec:torsion-free` prints and does not prove is
proved here, at the universe and the generality
`TorsionFreePrinted.HullPrintedInputs` asks for.  It is no longer an input to
anything: `hullPrintedInputs_of_smallCancellation` fills the field. -/
theorem osinLemma71Printed : OsinLemma71Printed.{u} := by
  intro G _ A htf N _ hN
  exact actsNonElementarily_of_torsionFree_of_ne_bot A htf N hN

#audit_closed_axioms osinLemma71Printed

/-! ## The printed sentence, closed -/

/-- **The printed sentence of `lem:saturation` that cites Osin's Lemma 7.1**, as
a closed proposition.

> The subgroup `N` is normal, and it is infinite because `G` is torsion-free and
> `N ≠ 1`, so it acts non-elementarily on `Cay(G,A)` by Osin [Lemma 7.1].

Both clauses, quantified inside the proposition: `N` is infinite, and `N` acts
non-elementarily on `Γ(G,A)`. -/
def SaturationOsinSentence : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G), IsPowerTorsionFree G →
    ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ →
      (N : Set G).Infinite ∧ ActsNonElementarily N (Cayley.base A.alphabet)

/-- **The printed sentence, with no citation left in it.**

`TorsionFreePrintedSentences.manuscriptSentence_saturationOsinNonElementary`
carries the second clause with `OsinLemma71Printed` as a hypothesis; this
carrier has no hypothesis beyond the printed three.  The first clause is
`infinite_coe_of_torsionFree_of_ne_bot`, already a theorem. -/
theorem manuscriptSentence_saturationOsinClosed : SaturationOsinSentence.{u} := by
  intro G _ A htf N _ hN
  exact ⟨infinite_coe_of_torsionFree_of_ne_bot htf hN,
    actsNonElementarily_of_torsionFree_of_ne_bot A htf N hN⟩

#audit_closed_axioms manuscriptSentence_saturationOsinClosed

/-! ## The printed bundle needs only Hull's Theorem 7.1 -/

/-- **`HullPrintedInputs` out of its small-cancellation field alone.**

`sec:torsion-free` prints three citations.  Hull's Corollary 5.7 with Lemma 5.8
was already a theorem over a torsion-free ambient group
(`hullSuitablePair_of_torsionFree`), which is why `HullPrintedInputs` has two
fields rather than three; Osin's Lemma 7.1 is `osinLemma71Printed` above.  So
one citation remains, and this is the wrapper that says so. -/
def hullPrintedInputs_of_smallCancellation
    (h : HullSmallCancellationPrinted.{u}) : HullPrintedInputs.{u} where
  smallCancellation := h
  osinNonElementary := osinLemma71Printed

/-- **The bundle of printed citations is exactly Hull's Theorem 7.1.**

The reverse direction is the first projection, so the two-field bundle the
section's proofs consume carries no information beyond `thm:hull`. -/
theorem nonempty_hullPrintedInputs_iff :
    Nonempty HullPrintedInputs.{u} ↔ HullSmallCancellationPrinted.{u} :=
  ⟨fun h => h.some.smallCancellation,
    fun h => ⟨hullPrintedInputs_of_smallCancellation h⟩⟩

#audit_closed_axioms nonempty_hullPrintedInputs_iff

end OsinPrinted
end GGT
end GroupApproximation
