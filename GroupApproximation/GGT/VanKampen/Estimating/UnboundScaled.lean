import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.GGT.VanKampen.Estimating.UnboundParameters

/-!
# The unbound estimate carrying Osin's geometric scale

`EstimatingUnboundOutputStatement` (`Estimating/Assembly.lean`) is **false**, and
this repository proves it twice, independently, at the same universes:

* `UnboundSmallMuCounterexample.not_estimatingUnboundOutputStatement`, over
  `S₃ × ℤ`, and
* `UnboundConjugateCounterexample.not_estimatingUnboundOutputStatement`, over
  `S₃`.

Both remain in the tree, refuted and reachable; nothing here changes or retires
them.  This module adds the repaired interface alongside, in the pattern
`Estimating/UnboundRepaired.lean` already established for the previous round.

## Why adding hypotheses does not repair it, and what does

The natural repair — assert hyperbolicity and Osin's parameter ranges — **does
not work**, and it is worth being precise about why, because the failure is not
obvious.  The stronger counterexample already satisfies Cayley hyperbolicity
with a proved four-point constant `1`, already has `0 < mu < 1/16` at
`mu = 1/32`, and already has `rho > mu⁻²` at `rho = 1089`.  It fails only the
*density* margin.

What excludes both models is `UnboundEstimate.OsinUnboundScale`'s `density_large`
field, `max (1000 * eps) c2 < lambda * sqrt rho / 240 - c`, and it excludes them
for a reason that does not depend on the geometric constants at all.  Its left
side is at least `1000 * eps ≥ 0` because `eps : ℕ`, while the density quantity
is negative in both models:

* small-mu: `lambda = 1`, `rho = 1089`, `c = 1089`, so
  `1 * 33 / 240 - 1089 < 0`;
* conjugate: `lambda = 1`, `rho = 1`, `c = 1`, so `1 * 1 / 240 - 1 < 0`.

So no choice of `kappa`, `c1`, `c2` can satisfy the certificate at either
model's parameters.  This is the whole content of the repair: the refutations
exploit parameter tuples for which Osin's density estimate never holds, and the
certificate is exactly the hypothesis that rules them out.

## Selection and unbound must share the choice

`Assembly.estimatingDataConstruction_of_components` already `obtain`s `eps` and
`rho` from the selection statement and applies the unbound statement **only** at
those, so the universal quantification over `eps` and `rho` that the
counterexamples exploit is never used by the one call site.  Narrowing the
unbound statement to selection's output is therefore compatible with its
consumer by construction rather than by hope — but only if selection *emits* the
certificate, which is why `EstimatingSelectionScaledConstructionStatement` is
strengthened in the same step.  Repairing either alone would leave the density
and shortening margins unavailable at the point they are needed.

## What this module does NOT do

It does not prove either statement, and it is not progress on the geometry.  The
producer remains open: the complementary-region decomposition with its incidence
and cutting bounds, G-cell padding and embedded surgery, general insertion
planarity, and the contradiction to maximal contiguity or minimal cutting-path
length are all untouched (issue #198).  This module converts a *refuted*
admission into an *open* one, which is worth doing because the first cannot be
discharged by anyone and the second can be worked, but it brings Theorem C no
closer on its own.

It also does not resolve a **second, independent defect** recorded in #198 and
not addressed by any parameter change: Osin's condition (*) ranges over *every*
distinguished system on the diagram, whereas the stored `EstimatingGraphData`
certificate concerns only the supplied scaffold.  The proof changes distinguished
systems and O-equivalent diagrams, so that quantifier needs review on its own
terms; carrying the scale does nothing about it.

## Main declarations

* `EstimatingSelectionScaledConstructionStatement` — selection, emitting the scale.
* `EstimatingUnboundScaledStatement` — the unbound estimate, consuming it.
* `estimatingDataConstruction_of_scaledComponents` — the same reduction as
  `estimatingDataConstruction_of_components`, over the scaled pair.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open UnboundEstimate

universe u w v

/-- **Selection, emitting Osin's scale certificate.**  Identical to
`EstimatingSelectionConstructionStatement` except that the chosen `eps` and
`rho` now come with the geometric constants and the `OsinUnboundScale`
inequalities, which subsume the bare `0 < rho` and `1 ≤ 2 * mu * sqrt rho` the
unscaled form carried. -/
def EstimatingSelectionScaledConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    (∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
      ∀ lambda c mu : ℝ,
        0 < lambda → lambda ≤ 1 → 0 ≤ c →
        0 < mu → mu ≤ 1 / 16 →
          ∃ (eps rho : ℕ) (kappa c1 c2 : ℝ),
            OsinUnboundScale lambda c mu kappa c1 c2 eps rho ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              OsinCCondition D W eps mu lambda c rho →
                ∀ Delta : DiscDiagram.{u, w, v} W,
                  Delta.Reduced → 0 < Delta.rCellCount →
                  IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
                    ∃ Delta' : DiscDiagram.{u, w, v} W,
                      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
                        Delta'.Reduced ∧
                        ∃ scaffold : EstimatingScaffold D eps Delta',
                          Nonempty (EstimatingGraphData D eps Delta' scaffold)

/-- **The unbound estimate at a scale Osin's argument actually supplies.**

The conclusion is verbatim that of `EstimatingUnboundOutputStatement`.  The
hypotheses gain hyperbolicity of the Cayley graph and, in place of the lone
threshold `1 ≤ 2 * mu * sqrt rho`, the full `OsinUnboundScale` certificate:
equation (36)'s `c1 + 2 * kappa < eps`, positivity of `rho`, the density
inequality, and the strict shortening margin.

Hyperbolicity alone would not repair the statement — both counterexamples
satisfy it — and neither would the parameter ranges; see this module's header
for the density argument that does. -/
def EstimatingUnboundScaledStatement : Prop :=
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
      ∃ Delta' : DiscDiagram.{u, w, v} W,
        Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
          Delta'.Reduced ∧
          ∃ scaffold' : EstimatingScaffold D eps Delta',
            Nonempty (EstimatingGraphData D eps Delta' scaffold') ∧
              Nonempty (Lemma62Data D eps mu rho Delta' scaffold')

/-- **The same reduction as `estimatingDataConstruction_of_components`, over the
scaled pair.**  The proof is that one with the certificate threaded from
selection's output to the unbound estimate's hypothesis; `0 < rho` now comes
from the certificate's own `rho_pos` field rather than from a separate
conjunct. -/
theorem estimatingDataConstruction_of_scaledComponents
    (hselection : EstimatingSelectionScaledConstructionStatement.{u, w, v})
    (hpieces : EstimatingPieceConstructionStatement.{u, w, v})
    (hunbound : EstimatingUnboundScaledStatement.{u, w, v}) :
    EstimatingDataConstructionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, kappa, c1, c2, hscale, hselect⟩ :=
    hselection D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hscale.rho_pos, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  obtain ⟨Delta', hequiv, hred', scaffold, graph⟩ := hselect W hcondition Delta
    hred hcells hboundary
  obtain ⟨equiv⟩ := hequiv
  obtain ⟨graph⟩ := graph
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord :=
    equiv.boundary_quasiGeodesic hboundary
  have hcells' : 0 < Delta'.rCellCount := by
    have hcount : Delta'.rCellCount = Delta.rCellCount := equiv.rCellCount_eq
    omega
  obtain ⟨Delta'', hequiv', hred'', scaffold', graph', unbound⟩ :=
    hunbound D eps rho mu lambda c kappa c1 c2 hhyper hscale hcondition Delta'
      hred' hcells' scaffold graph hboundary'
  obtain ⟨equiv'⟩ := hequiv'
  obtain ⟨graph'⟩ := graph'
  obtain ⟨unbound⟩ := unbound
  obtain ⟨pieces⟩ := hpieces D eps Delta'' scaffold' hred''
  exact ⟨Delta'', ⟨equiv.trans equiv'⟩,
    EstimatingData.nonempty_of_certificates scaffold' graph' pieces unbound
      hcondition⟩

/-! Printed on every build.  Without this the probe's `sorryAx: none` would be
vacuous for this file: that check reports only on declarations whose axiom line
the build actually emits. -/

#print axioms estimatingDataConstruction_of_scaledComponents

end VanKampen
end GGT
end GroupApproximation
