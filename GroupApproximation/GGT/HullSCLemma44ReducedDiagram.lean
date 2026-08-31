import GroupApproximation.GGT.HullSCLemma44RelatorDiagram
import GroupApproximation.GroupTheory.NormalClosureReducedProduct

/-!
# Reduced least-area diagrams for Hull's Lemma 4.4

This is the cancellation step after the short-boundary reduction.  The
tree-shaped normal-closure certificate is flattened into its ordered list of
signed conjugate relators.  Least area makes that list reduced: no nonempty
consecutive collection of cells has trivial product, since it could otherwise
be deleted to give a smaller filling of the same boundary.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- The flat, reduced form of a least-area Lemma 4.4 boundary certificate. -/
structure Lemma44ReducedRelatorDiagram {G : Type u} [Group G]
    {Λ : Type w} (A : Alphabet G)
    (W : Set (List (GGT.RelLetter G Λ))) (R : ℕ)
    extends Lemma44RelatorDiagramBoundary A W R where
  factors : List G
  factors_length : factors.length = area
  factors_prod : factors.prod = boundary
  factors_signed : ∀ x ∈ factors, RelatorDefectBudget.IsSignedConjugate
    (GGT.RelLetter.listVal '' W) x
  reduced : ∀ pre mid suf : List G,
    factors = pre ++ mid ++ suf →
      mid ≠ [] → mid.prod ≠ 1
  no_cancelling_pair : ∀ pre between suf : List G, ∀ x y : G,
    factors = pre ++ x :: (between ++ y :: suf) →
      (between.prod)⁻¹ * x * between.prod * y ≠ 1

/-- Flatten a least-area boundary certificate and spend its minimality to
obtain the reduced-diagram cancellation condition. -/
theorem Lemma44RelatorDiagramBoundary.exists_reduced
    {G : Type u} [Group G] {Λ : Type w} {A : Alphabet G}
    {W : Set (List (GGT.RelLetter G Λ))} {R : ℕ}
    (D : Lemma44RelatorDiagramBoundary A W R) :
    Nonempty (Lemma44ReducedRelatorDiagram A W R) := by
  obtain ⟨factors, hlen, hprod, hcells⟩ := D.isRelatorProduct.exists_flatten
  exact ⟨{
    toLemma44RelatorDiagramBoundary := D
    factors := factors
    factors_length := hlen
    factors_prod := hprod
    factors_signed := hcells
    reduced := RelatorDefectBudget.no_trivial_subproduct_of_minimal
      hlen hprod hcells D.area_minimal
    no_cancelling_pair := RelatorDefectBudget.no_cancelling_pair_of_minimal
      hlen hprod hcells D.area_minimal
  }⟩

/-- Failure of ball injectivity therefore produces a short nontrivial reduced
least-area relator diagram. -/
theorem exists_lemma44ReducedRelatorDiagram_of_not_injOn
    {G : Type u} [Group G] {Λ : Type w} (A : Alphabet G)
    (W : Set (List (GGT.RelLetter G Λ))) (R : ℕ)
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hnot : ¬ Set.InjOn q
      (Manuscript.NonMF.TorsionFree.cayleyBall A R)) :
    Nonempty (Lemma44ReducedRelatorDiagram A W R) := by
  obtain ⟨D⟩ := exists_lemma44RelatorDiagramBoundary_of_not_injOn
    A W R q hker hnot
  exact D.exists_reduced

end HullSC
end GroupApproximation
