import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBoundCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: side chunks bounded by ε

Lane `gl-p07-11`.  Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`); certifies no printed sentence on its
own (it feeds `thm:hull`, tex 2122/2129, through Osin's Lemma 9.7(b)).

`PocketSideBoundStatement` is the lane statement over region candidates: the far sides are
`a.sideFrom j` and `b.sideFrom i`, each of length at most `ε` (`RegionCandidate.sideFrom_length_le`).
It takes lane 10's four-piece decomposition as hypotheses (a duplicate-free outside walk, a rotation
whose inverse walk reads `R₁ ++ U₁ ++ R₂ ++ U₂`, and the far-side case split), so it does not
depend on lane 10 being on disk.  It is proved outright: `pocketSideBound`, by
`SideBound.exists_bounded_fourPiece` (see `SideBoundCore.lean` for the argument).

The Hyp-level reduction from lane 10's output is `SideBoundPocket.lean`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded HullSC WordMetric

/-- **Side chunks bounded by ε.**  Let `outerWalk` be duplicate free, and let the inverse walk of a
rotation of it read `R₁ ++ U₁ ++ R₂ ++ U₂`, where the reverse of every dart of `R₁` lies on one far
side (`a.sideFrom j` or `b.sideFrom i`) and likewise for `R₂`; or, when a run `U₁` or `U₂` is
empty, the reverse of every dart of `R₁ ++ R₂` lies on some far side.  Then the inverse walk of a
rotation reads `S₁ ++ V₁ ++ S₂ ++ V₂` with `|S₁|, |S₂| ≤ ε` and runs `V₁, V₂ = U₁, U₂`, or, when
`U₂` was empty, `V₁ = []` and `V₂ = U₁`. -/
def PocketSideBoundStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount)
    (a b : RegionCandidate D eps X) (outerWalk : List X.toCombMap.Dart) (n : ℕ)
    (R₁ U₁ R₂ U₂ : List X.toCombMap.Dart),
    outerWalk.Nodup →
    invDarts X (outerWalk.rotate n) = R₁ ++ U₁ ++ R₂ ++ U₂ →
    (((∀ r ∈ R₁, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
          (∀ r ∈ R₁, X.toCombMap.alpha r ∈ b.sideFrom i)) ∧
        ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ a.sideFrom j) ∨
          (∀ r ∈ R₂, X.toCombMap.alpha r ∈ b.sideFrom i))) ∨
      ((∀ r ∈ R₁ ++ R₂,
          X.toCombMap.alpha r ∈ a.sideFrom j ∨ X.toCombMap.alpha r ∈ b.sideFrom i) ∧
        (U₁ = [] ∨ U₂ = [])) →
    ∃ (m : ℕ) (S₁ V₁ S₂ V₂ : List X.toCombMap.Dart),
      invDarts X (outerWalk.rotate m) = S₁ ++ V₁ ++ S₂ ++ V₂ ∧ S₁.length ≤ eps ∧
        S₂.length ≤ eps ∧ ((V₁ = U₁ ∧ V₂ = U₂) ∨ (U₂ = [] ∧ V₁ = [] ∧ V₂ = U₁))

/-- **Side chunks bounded by ε**, proved. -/
theorem pocketSideBound : PocketSideBoundStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j a b outerWalk n R₁ U₁ R₂ U₂ hw hdec hcase
  exact SideBound.exists_bounded_fourPiece hw (a.sideFrom_length_le j) (b.sideFrom_length_le i)
    hdec hcase

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketSideBoundStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pocketSideBound
