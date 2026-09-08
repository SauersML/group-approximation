import GroupApproximation.GGT.VanKampen.Estimating.UnboundComponentSplit
import GroupApproximation.GGT.VanKampen.Estimating.UnboundConstruction

/-!
# Osin Appendix Lemma 62's geometric residue, at his scale

`Lemma62ComponentDecompositionStatement` is the complementary decomposition
with its `1/60` density bound, and it is **false**: it quantifies `rho` with no
scale premise, so `UnboundSmallMuCounterexample.not_lemma62ComponentDecomposition-
Statement` refutes it.  This file states the same conclusion at the scale Osin's
argument actually supplies, which is the shape the repair of `c685697b9` gave
`EstimatingUnboundOutputStatement`, and derives that statement from it.

## Why the refutations do not reach this one

Adding hypotheses weakens a statement, so nothing is inherited automatically --
but the two counterexamples are excluded for a reason, not by accident.  Both
violate `OsinUnboundScale.density_large`, whose left side is at least
`1000 * eps >= 0`:

* small-mu, at `lambda = 1`, `rho = 1089`, `c = 1089`: `33 / 240 - 1089 < 0`;
* conjugate, at `lambda = 1`, `rho = 1`, `c = 1`: `1 / 240 - 1 < 0`.

So no choice of `kappa`, `c1`, `c2` satisfies the certificate at either model.

## What is still open, and what is not

Everything above the decomposition is proved and composes here: the averaging
inequality (`componentPartition_of_components`), Lemma 61's planar counting, the
`53n` arc budget, and the conversion of a certificate into `Lemma62Data`
(`lemma62Data_of_partitionCertificate`).  The numerical `threshold` field is
`OsinUnboundScale.threshold` verbatim.

**This file discharges none of the geometry.**  It names the residue at a
statement that is not refuted, where the previous name was, and wires it to the
consumer.  Two obligations remain inside it, neither individually assignable
yet: constructing `ComplementaryComponents` from an actual `Delta` -- the only
inhabitant on `origin/main` is `complementaryComponents_oneCell_model`, which
requires `unboundTotal = 0` -- and contradicting `DistinguishedFamily.weight_maximal`
or `card_minimal` with the connector pair that `unboundComponentWordPolygons`
produces.  Issue #198.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open UnboundEstimate

universe u w v

/-- **Osin Appendix Lemma 62's geometric residue, carrying his scale.**  The
complementary decomposition exists and no component reaches the `1/60` density
threshold, under hyperbolicity and `OsinUnboundScale`.

This supersedes `Lemma62ComponentDecompositionStatement`, which states the same
conclusion without the scale and is refuted.  Do not restate this without
`_hscale`: `density_large` is the only hypothesis that excludes the two
counterexamples, and without it the statement is false rather than open. -/
def Lemma62ScaledDecompositionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c kappa c1 c2 : ℝ)
    (_hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (_hscale : OsinUnboundScale lambda c mu kappa c1 c2 eps rho)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (_hred : Delta.Reduced)
    (_hcells : 0 < Delta.rCellCount)
    (scaffold : EstimatingScaffold D eps Delta)
    (_graph : EstimatingGraphData D eps Delta scaffold),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      ∃ components : ComplementaryComponents scaffold,
        ∀ i : Fin components.count,
          components.unboundLength i <
            (components.arcCount i : ℝ) * Real.sqrt (rho : ℝ) / 60

/-- The scaled decomposition gives `Lemma62Data` on the supplied scaffold.  The
strict budget comes from the averaging inequality; the numerical threshold is
`OsinUnboundScale.threshold` verbatim, so no second numerical premise appears. -/
theorem lemma62Data_of_scaledDecomposition
    (hdecomp : Lemma62ScaledDecompositionStatement.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c kappa c1 c2 : ℝ)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hscale : OsinUnboundScale lambda c mu kappa c1 c2 eps rho)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (hred : Delta.Reduced)
    (hcells : 0 < Delta.rCellCount)
    (scaffold : EstimatingScaffold D eps Delta)
    (graph : EstimatingGraphData D eps Delta scaffold)
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  have hrhoReal : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast hscale.rho_pos
  have hsqrt : 0 < Real.sqrt (rho : ℝ) := Real.sqrt_pos.2 hrhoReal
  obtain ⟨components, hdensity⟩ :=
    hdecomp D eps rho mu lambda c kappa c1 c2 hhyper hscale hcondition Delta hred
      hcells scaffold graph hboundary
  obtain ⟨certificate⟩ :=
    componentPartition_of_components components hcells hsqrt hdensity
  exact lemma62Data_of_partitionCertificate certificate hscale.threshold

/-- **The consumer.**  The scaled decomposition proves the repaired unbound
output statement, with the identity diagram: `OEquivalentDiscDiagram.refl`
supplies the equivalence, `_hred` the reducedness, and the supplied
`EstimatingGraphData` its own clause, so no diagram surgery is required of the
producer even though Osin's argument performs one. -/
theorem estimatingUnboundOutputStatement_of_scaledDecomposition
    (hdecomp : Lemma62ScaledDecompositionStatement.{u, w, v}) :
    EstimatingUnboundOutputStatement.{u, w, v} := by
  intro G _ Lambda D eps rho mu lambda c kappa c1 c2 hhyper hscale W hcondition
    Delta hred hcells scaffold graph hboundary
  exact ⟨Delta, ⟨OEquivalentDiscDiagram.refl Delta⟩, hred, scaffold, ⟨graph⟩,
    lemma62Data_of_scaledDecomposition hdecomp D eps rho mu lambda c kappa c1 c2
      hhyper hscale hcondition Delta hred hcells scaffold graph hboundary⟩

/-- Model check at the empty relator family: the positive-cell premise is
impossible there, so the conclusion holds and the statement is not vacuous for
the trivial reason that its hypotheses cannot be met. -/
theorem lemma62ScaledDecomposition_emptyFamily_model
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (scaffold : EstimatingScaffold D eps Delta)
    (hcells : 0 < Delta.rCellCount) :
    ∃ components : ComplementaryComponents scaffold,
      ∀ i : Fin components.count, components.unboundLength i < 0 :=
  (no_positive_rCells_emptyFamily Delta hcells).elim

end Estimating
end VanKampen
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.Estimating.lemma62Data_of_scaledDecomposition
#audit_axioms GroupApproximation.GGT.VanKampen.Estimating.estimatingUnboundOutputStatement_of_scaledDecomposition
#audit_axioms GroupApproximation.GGT.VanKampen.Estimating.lemma62ScaledDecomposition_emptyFamily_model
