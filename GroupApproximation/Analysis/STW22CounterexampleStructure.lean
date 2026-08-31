import GroupApproximation.Analysis.STW22ProbabilitySimplexBauer
import GroupApproximation.Analysis.STW22TypeIBlocks

/-!
# Sections 1 and 3 of the STW Problem XXII counterexample audit, assembled

`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`
sections 1 and 3 make two structural assertions about the algebra
`A = (⨁_{c₀} D s)⁺`, `D s = Γ(End(1 ⊕ L_s^{⊕s}))`:

* **(A5)** `A` is type I, because each `D s` is (its fibres are `M_(s+1)`) and
  type I passes through countable `c₀`-sums and unitization;
* **(A6)** `T(A) = Prob(K)` with `∂ₑ T(A) = K` for `K` the one-point
  compactification of `⨆ₛ CP^(s²)`, so `T(A)` is Bauer.

`counterexample_typeI_and_bauer` states both at once, from the two interfaces
proved in `Analysis/STW22TypeIBlocks` and `Analysis/STW22ProbabilitySimplexBauer`.

## What the hypotheses are

* `hI : HomogeneousBlockTypeIInputs d D B A` carries (A5).  Its homogeneity
  clause is a statement about the blocks; its two permanence clauses are the
  classical facts Mathlib cannot yet supply.  `homogeneousBlockTypeIInputs_model`
  shows the bundle is satisfiable.
* The map `e` carries the identification `T(A) ≅ Prob(K)`: an injective,
  additive, `ℝ≥0`-homogeneous, continuous map from the finite measures on `K`
  into the ambient space of the trace simplex.  Every *convexity* consequence
  the audit draws from that identification is derived here; nothing about
  traces is assumed beyond the map itself.

The topological hypotheses on `K` — compact, Hausdorff, second countable, Borel
— are exactly what the audit's `K` satisfies: it is compact metrizable, being
the one-point compactification of a countable disjoint union of compact
metrizable spaces.  Formalising `CP^(s²)` and that compactification is not
attempted here; `K` is left abstract with those instances assumed.
-/

namespace GroupApproximation
namespace STW22

open MeasureTheory Set

open scoped NNReal

noncomputable section

/-- **Audit sections 1 and 3.**  Under the counterexample's type I inputs and an
affine identification of the trace simplex with `Prob(K)`:

1. `A` is type I;
2. the trace simplex is compact, convex, and has a closed extreme boundary —
   the Bauer clause;
3. its extreme boundary is the copy of `K` given by the Dirac masses. -/
theorem counterexample_typeI_and_bauer
    {d : ℕ → ℕ} {D : ℕ → Type} [∀ s, CStarAlgebra (D s)]
    {B : Type} [CStarAlgebra B] {A : Type} [CStarAlgebra A]
    (hI : HomogeneousBlockTypeIInputs d D B A)
    {K : Type} [MeasurableSpace K] [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] [CompactSpace K] [HasOuterApproxClosed K]
    {V : Type} [AddCommMonoid V] [SMul ℝ≥0 V] [TopologicalSpace V] [T2Space V]
    (e : FiniteMeasure K → V) (hcont : Continuous e) (hinj : Function.Injective e)
    (hadd : ∀ x y : FiniteMeasure K, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℝ≥0) (x : FiniteMeasure K), e (c • x) = c • e x) :
    IsTypeI A ∧ IsCompactConvexClosedBoundary ℝ≥0 (e '' probSimplex K) ∧
      (e '' probSimplex K).extremePoints ℝ≥0 = Set.range (fun x : K => e (diracFM x)) :=
  ⟨hI.isTypeI,
    isCompactConvexClosedBoundary_of_probSimplex_image e hcont hinj hadd hsmul,
    extremePoints_probSimplex_image e hinj hadd hsmul⟩

/-- The Bauer conclusion in full, once the Choquet clause is supplied for the
transported simplex. -/
theorem counterexample_isBauerSimplex
    {K : Type} [MeasurableSpace K] [TopologicalSpace K] [T2Space K]
    [SecondCountableTopology K] [BorelSpace K] [CompactSpace K] [HasOuterApproxClosed K]
    {V : Type} [AddCommMonoid V] [SMul ℝ≥0 V] [TopologicalSpace V] [T2Space V]
    (e : FiniteMeasure K → V) (hcont : Continuous e) (hinj : Function.Injective e)
    (hadd : ∀ x y : FiniteMeasure K, e (x + y) = e x + e y)
    (hsmul : ∀ (c : ℝ≥0) (x : FiniteMeasure K), e (c • x) = c • e x)
    (hchoquet : IsChoquetSimplex ℝ≥0 (e '' probSimplex K)) :
    IsBauerSimplex ℝ≥0 (e '' probSimplex K) :=
  ⟨hchoquet, isCompactConvexClosedBoundary_of_probSimplex_image e hcont hinj hadd hsmul⟩

end

end STW22
end GroupApproximation
