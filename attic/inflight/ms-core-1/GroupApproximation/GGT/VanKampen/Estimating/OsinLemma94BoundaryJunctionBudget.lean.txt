import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the boundary bad junctions, backward junctions and value failures

Osin (math/0411039v3, §9), proof of Lemma 9.4.  ms-inverses-3's bad-junction reduction
(`Estimating/OsinLemma94BadJunctionExclusion`) leaves `OsinLemma94BoundaryJunctionBudgetInput`: summed over the
relator polygons with at least two class non-joins, the boundary bad junctions number at most `K n`.

A boundary bad junction joins two consecutive sides on one section at kind level but not at class level.  Its gap is
the stretch of `∂Δ` strictly between the two sides (`ClassProducer.boundaryGapOf`).  It fails the class join in one
of two disjoint ways.
* **Backward junction** (`JunctionBackward`): the next side starts no later along `outerDarts` than the previous side
  ends, so the forward stretch between them wraps the base index of `outerDarts`.  `boundaryGapOf` subtracts in `ℕ`,
  so the gap is `[]`, of value one.
* **Value failure**: the gap is a forward lobe of `∂Δ` at a pinch vertex, reading a value other than `1`.

This module fixes the two kinds and reduces the budget to one count for each.

* `backwardJunctions`, `valueFailureJunctions`, and `boundaryBadJunctions_subset_union`.
* Residual pieces, with the binders of `OsinLemma94BoundaryJunctionBudgetInput`:
  - `OsinLemma94BackwardJunctionCountInput`: at most `n + 1` backward junctions;
  - `OsinLemma94BoundaryValueFailureCountInput`: at most `n` value failures.
* `osinLemma94BoundaryJunctionBudgetInput_of_pieces`: the budget with `K = 3`, since `2n + 1 ≤ 3n` for `0 < n`.

Model test (hand, `notes/nm-swarm/reports/ms-core-1.md`).  "At most one backward junction" fails.  Nested lobes
`L₁ ⊃ L₂` of `∂Δ`, both containing the base index, seen by relator polygons `k₁` outside `L₁` and `k₂` in `L₁ \ L₂`,
give two backward junctions.  One polygon has at most one, and across nesting levels the owner of `L_{i+1}` has a
cell side in `L_i \ L_{i+1}`, so the count is at most `n + 1`.  Value failures get private relator cells along the
laminar family of forward lobes, so they number at most `n`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4 inside the proof of
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94RealizedPolygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **A backward junction**: the next side starts no later along `outerDarts` than side `s` ends. -/
def JunctionBackward (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (s : ℕ) : Prop :=
  ∃ e ∈ (P.sideDarts k s).getLast?, ∃ e' ∈ (P.sideDarts k ((s + 1) % P.sideCount k)).head?,
    (outerDarts S.diagram).idxOf e' ≤ (outerDarts S.diagram).idxOf e

/-- The backward boundary bad junctions of polygon `k`. -/
noncomputable def backwardJunctions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) : Finset ℕ :=
  (P.boundaryBadJunctions k).filter fun s => P.JunctionBackward k s

/-- The boundary bad junctions of polygon `k` whose gap reads a value other than `1`. -/
noncomputable def valueFailureJunctions (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) : Finset ℕ :=
  (P.boundaryBadJunctions k).filter fun s =>
    RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) ≠ 1

/-- **Every boundary bad junction is backward or a value failure.**  For a boundary side the cell face clause of
`ClassJoins` is vacuous, so a kind-level join with gap value one fails the class join only through the forward
clause. -/
theorem boundaryBadJunctions_subset_union (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    P.boundaryBadJunctions k ⊆ P.backwardJunctions k ∪ P.valueFailureJunctions k := by
  intro s hs
  by_cases hval : RelLetter.listVal (dartWord S.diagram (P.junctionGap k s)) = 1
  · refine Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hs, ?_⟩)
    obtain ⟨hbad, j, hj⟩ := Finset.mem_filter.1 hs
    obtain ⟨-, hjoin, hnot⟩ := Finset.mem_filter.1 hbad
    by_contra hnb
    refine hnot ⟨hjoin, hval, fun j' hj' => ?_, fun j' _ e he e' he' => ?_⟩
    · rw [hj] at hj'
      cases hj'
    · exact not_le.1 fun hle => hnb ⟨e, he, e', he', hle⟩
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hs, hval⟩)

theorem card_boundaryBadJunctions_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (P.boundaryBadJunctions k).card ≤ (P.backwardJunctions k).card + (P.valueFailureJunctions k).card :=
  (Finset.card_le_card (P.boundaryBadJunctions_subset_union k)).trans (Finset.card_union_le _ _)

end OsinLemma94RealizedPolygons

/-- **Backward junctions (residual).**  At the parameters of Lemma 9.4, for `ρ` large, with clause (b) of Lemma 9.7
below the number of relator cells of `Δ`: summed over the polygons with an (A1) side and at least two class
non-joins, the backward junctions number at most `n + 1`. -/
def OsinLemma94BackwardJunctionCountInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∑ k ∈ P.relatorPolygons.filter (fun k =>
                        2 ≤ ((Finset.range (P.sideCount k)).filter
                          fun s => ¬ P.ClassJoins k s).card),
                      (P.backwardJunctions k).card ≤ Delta.rCellCount + 1

/-- **Value failures at boundary junctions (residual).**  With the same binders: summed over the polygons with an
(A1) side and at least two class non-joins, the value failures number at most `n`. -/
def OsinLemma94BoundaryValueFailureCountInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ (Delta : DiscDiagram.{u, w, v} W)
              (cuts : SectionCuts D lambda c Delta.boundaryWord),
              Delta.LeastArea → 0 < Delta.rCellCount →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
                S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1) → S.DartMinimal →
                  ∀ P : OsinLemma94RealizedPolygons S, P.Maximal →
                    ∑ k ∈ P.relatorPolygons.filter (fun k =>
                        2 ≤ ((Finset.range (P.sideCount k)).filter
                          fun s => ¬ P.ClassJoins k s).card),
                      (P.valueFailureJunctions k).card ≤ Delta.rCellCount

/-- **The boundary junction budget from its two counts**, with `K = 3`: `(n + 1) + n ≤ 3n` for `0 < n`. -/
theorem osinLemma94BoundaryJunctionBudgetInput_of_pieces
    (hback : OsinLemma94BackwardJunctionCountInput.{u, w, v})
    (hval : OsinLemma94BoundaryValueFailureCountInput.{u, w, v}) :
    OsinLemma94BoundaryJunctionBudgetInput.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hl hl1 hc hmu hmu16
  obtain ⟨e1, he1⟩ := hback D hhyp lambda c mu hl hl1 hc hmu hmu16
  obtain ⟨e2, he2⟩ := hval D hhyp lambda c mu hl hl1 hc hmu hmu16
  refine ⟨max e1 e2, fun eps heps => ?_⟩
  obtain ⟨r1, hr1, hb⟩ := he1 eps (le_trans (le_max_left _ _) heps)
  obtain ⟨r2, hr2, hv⟩ := he2 eps (le_trans (le_max_right _ _) heps)
  refine ⟨3, max r1 r2, lt_of_lt_of_le hr1 (le_max_left _ _),
    fun rho hrho W hW Delta cuts hla hpos hind S hS hmin P hmax => ?_⟩
  have h1 := hb rho (le_trans (le_max_left _ _) hrho) W hW Delta cuts hla hpos hind S hS hmin P hmax
  have h2 := hv rho (le_trans (le_max_right _ _) hrho) W hW Delta cuts hla hpos hind S hS hmin P hmax
  refine (Finset.sum_le_sum fun k _ => P.card_boundaryBadJunctions_le k).trans ?_
  rw [Finset.sum_add_distrib]
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94RealizedPolygons.boundaryBadJunctions_subset_union
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94BoundaryJunctionBudgetInput_of_pieces
