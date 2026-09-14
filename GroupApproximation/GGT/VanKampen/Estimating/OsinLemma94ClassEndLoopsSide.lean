import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSection
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 over the classes: the side clause of the end loops

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs of
type (A1) in `∂Δ_i`".  The residual `OsinLemma94ClassEndLoopsInput`
(`Estimating/OsinLemma94ClassSection`) has four clauses: the other-class budget, the side clause
`hside`, the bounds on the end loops, and `hbubble`.  The side clause says that an unbound dart
facing no selected region and not its own cell lies across an (A1) side.  It holds for every
globally distinguished family, through lemmas already on main.

* `GloballyDistinguishedSectionFamily.alpha_faceOf_not_cell_of_unbound`: across such a dart lies
  no relator cell and not the exterior, since otherwise the edge doubles into a digon region that
  contradicts `weight_maximal`.
* `OsinLemma94RealizedPolygons.exists_relatorSide_of_unbound`: the face across is then the face
  of a polygon, and the side through the reversed dart is of kind (A1).
* Their premises, `hvalue` and `hlen`, hold under `C(ε, μ, λ, c, ρ)` once `c < λ ρ` and `1 < ρ`
  (`cell_listVal_ne_one`, `one_lt_cellDarts_length`).

This module proves the side clause and states the residual with it removed.

* `GloballyDistinguishedSectionFamily.classEndLoops_side`: the side clause.
* `OsinLemma94ClassEndLoopsBudgetInput` (residual): the other-class budget, the end loops of at
  most `B` darts, and `hbubble`.
* `osinLemma94ClassEndLoopsInput_of_budget`: `OsinLemma94ClassEndLoopsInput` from the residual,
  with `ρ₀` raised to `max ρ₀ (⌈c/λ⌉₊ + 2)`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The side clause of the class end loops.**  Under `C(ε, μ, λ, c, ρ)` with `0 < λ`, `c < λ ρ`
and `1 < ρ`, for a globally distinguished family and realized polygons, every unbound dart that
faces no selected region and not its own cell lies across an (A1) side. -/
theorem classEndLoops_side (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (P : OsinLemma94RealizedPolygons S) {epsC : ℕ} {mu : ℝ} {rho : ℕ}
    (hW : OsinCCondition D W epsC mu lambda c rho) (hlambda : 0 < lambda)
    (hrhoc : c < lambda * rho) (hrho : 1 < rho) :
    ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
      d ∈ S.unboundOffRegions i →
        (cell S.diagram i).face ≠ S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) →
          ∃ k s, s < P.sideCount k ∧ s ∈ P.relatorSides k ∧
            S.diagram.toCombMap.alpha d ∈ P.sideDarts k s := by
  intro i d hd hsame
  have hvalue := S.cell_listVal_ne_one hW hlambda hrhoc
  have hlen := S.one_lt_cellDarts_length hW hrho
  have hunbound : d ∈ RegionCandidate.unboundDarts S.family i := (Finset.mem_filter.mp hd).1
  have hreg : ¬ ∃ a ∈ S.family,
      S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) ∈ a.1 :=
    (Finset.mem_filter.mp hd).2
  have hdcell : d ∈ cellDarts S.diagram i :=
    List.mem_toFinset.mp (Finset.mem_sdiff.mp hunbound).1
  obtain ⟨hcell, hout⟩ := S.alpha_faceOf_not_cell_of_unbound hvalue hlen hunbound hsame
  exact P.exists_relatorSide_of_unbound hvalue hdcell hcell hout hreg

end GloballyDistinguishedSectionFamily

/-- **The end loops of the class cover, without the side clause (residual).**  The hypotheses of
`OsinLemma94ClassEndLoopsInput`, with the same conclusion except the side clause, which
`GloballyDistinguishedSectionFamily.classEndLoops_side` proves: class polygons whose classes of
kind other than `cutting` number at most `K n` over the budget polygons, with end loops of at most
`B` darts carrying the reverses of the darts on single-class polygons that lie in no (A1) class of a
budget polygon. -/
def OsinLemma94ClassEndLoopsBudgetInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ K B : ℕ, ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
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
                    ∃ Q : OsinLemma94ClassPolygons P,
                      (∑ k ∈ Q.budgetPolygons, (Q.otherClasses k).card ≤
                        K * Delta.rCellCount) ∧
                      ∃ (classEnd : Fin P.count → ℕ → Bool → List S.diagram.toCombMap.Dart)
                        (regionEnd : RegionCandidate D eps S.diagram → Fin 4 →
                          List S.diagram.toCombMap.Dart),
                        (∀ k ∈ Q.budgetPolygons, ∀ i < Q.classCount k, ∀ b,
                          (classEnd k i b).length ≤ B) ∧
                        (∀ a ∈ S.family, ∀ t, (regionEnd a t).length ≤ B) ∧
                        ∀ (i : Fin S.diagram.rCellCount) (d : S.diagram.toCombMap.Dart),
                          d ∈ S.unboundOffRegions i →
                            (cell S.diagram i).face ≠
                                S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) →
                              ∀ k s, Q.classCount k = 1 → s < P.sideCount k →
                                s ∈ P.relatorSides k →
                                S.diagram.toCombMap.alpha d ∈ P.sideDarts k s →
                                  (∃ k' i', i' < Q.classCount k' ∧ i' ∈ Q.relatorClasses k' ∧
                                      S.diagram.toCombMap.alpha d ∈ Q.classDarts k' i') ∨
                                    (∃ k' ∈ Q.budgetPolygons, ∃ i' < Q.classCount k', ∃ b,
                                      S.diagram.toCombMap.alpha d ∈ classEnd k' i' b) ∨
                                    ∃ a ∈ S.family, ∃ t,
                                      S.diagram.toCombMap.alpha d ∈ regionEnd a t

/-- **The end loops from the residual without the side clause.**  The side clause comes from
`GloballyDistinguishedSectionFamily.classEndLoops_side`, at `ρ ≥ ⌈c/λ⌉₊ + 2`. -/
theorem osinLemma94ClassEndLoopsInput_of_budget
    (hbudget : OsinLemma94ClassEndLoopsBudgetInput.{u, w, v}) :
    OsinLemma94ClassEndLoopsInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, hL⟩ := hbudget D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨K, B, rho1, hrho1, hK⟩ := hL eps heps
  refine ⟨K, B, max rho1 (⌈c / lambda⌉₊ + 2), lt_of_lt_of_le hrho1 (le_max_left _ _),
    fun rho hrho => ?_⟩
  simp only [max_le_iff] at hrho
  obtain ⟨hr1, hrc⟩ := hrho
  intro W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax
  obtain ⟨Q, hother, classEnd, regionEnd, hclassEnd, hregionEnd, hbubble⟩ :=
    hK rho hr1 W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax
  have hrhoc : c < lambda * rho := by
    have hceil : c / lambda ≤ ⌈c / lambda⌉₊ := Nat.le_ceil _
    have hcast : ((⌈c / lambda⌉₊ : ℕ) : ℝ) + 1 ≤ rho := by
      exact_mod_cast (by omega : ⌈c / lambda⌉₊ + 1 ≤ rho)
    have hlt : c < rho * lambda := (div_lt_iff₀ hlambda).mp (by linarith)
    linarith [mul_comm lambda (rho : ℝ)]
  exact ⟨Q, hother, S.classEndLoops_side P hW hlambda hrhoc (by omega), classEnd, regionEnd,
    hclassEnd, hregionEnd, hbubble⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.classEndLoops_side
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ClassEndLoopsInput_of_budget
