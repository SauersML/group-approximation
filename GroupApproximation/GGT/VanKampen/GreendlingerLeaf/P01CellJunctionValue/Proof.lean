import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.Main
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingSideArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCutSuccProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCovers
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94BadJunctionExclusion
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: same-cell junction gaps read `1`

Target: `OsinLemma94CellJunctionValueInput`.

* `noCellInside`: a face set enclosed by an arc of a relator cell `C`, without `C`, holds no relator
  cell.  Otherwise the restricted loop cut `enclosedSubdiagramLoopCutSuccLong`, with the empty
  connector part, gives a loop cut, killed by least area and the clause below the number of relator
  cells (`OsinLoopCut.false_of_below`).
* `proof`: the thresholds `ρ ≥ 2`, `ρ ≥ ρ₁` of `SameCellSimplePocket.exists_rho_large`, and
  `ρ > c / λ` (relator words do not read `1`), then `main` (module `Main`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **No relator cell inside a pocket along a cell**, by the loop cut. -/
theorem noCellInside {G : Type u} [Group G] {Lambda : Type w} {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmu1 : mu ≤ 1 / 16) {eps rho : ℕ}
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ)) (hrho : 2 ≤ rho)
    {W : Set (List (RelLetter G Lambda))} (hW : OsinCCondition D W eps mu lambda c rho)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hleast : Delta.LeastArea)
    (hbelow : ∀ (Xi : DiscDiagram.{u, w, v} W) (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
      Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
        ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi, OsinLemma97bConclusion mu T)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts) :
    NoCellInside S.diagram := by
  intro F walk hF j hj A hA C hC hCF
  have hrho0 : 0 < rho := by omega
  have hlong := one_lt_length_of_two_le_rho hW hrho
  have hdec : invDarts S.diagram walk = [] ++ invDarts S.diagram A.darts := by
    rw [hA, List.nil_append]
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart))) ≤ eps := by
    rw [show RelLetter.listVal (dartWord S.diagram ([] : List S.diagram.toCombMap.Dart)) = 1
      from rfl, WordMetric.wordNorm_one]
    exact Nat.zero_le _
  obtain ⟨cut⟩ := enclosedSubdiagramLoopCutSuccLong D eps rho mu lambda c hW hlambda1 hc hlong
    Delta S.diagram hleast S.equiv S.label_admissible F walk hF C hC hCF j hj A [] hdec hnorm
  exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 hrho0 hlarge hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

/-- The ceiling threshold makes `c < λ ρ`. -/
theorem c_lt_lambda_mul {lambda c : ℝ} (hlambda : 0 < lambda) {rho : ℕ}
    (hrho : ⌈c / lambda⌉₊ + 1 ≤ rho) : c < lambda * (rho : ℝ) := by
  have h2 : ((⌈c / lambda⌉₊ + 1 : ℕ) : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr hrho
  push_cast at h2
  have hceil : c / lambda < (rho : ℝ) := by
    linarith [Nat.le_ceil (c / lambda)]
  have h3 := (div_lt_iff₀ hlambda).mp hceil
  rw [mul_comm]
  exact h3

/-- **Osin's Lemma 9.4: same-cell junction gaps read `1`.** -/
theorem proof : OsinLemma94CellJunctionValueInput.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max (max 2 rho1) (⌈c / lambda⌉₊ + 1), by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard hmin P _hmax k _hk h2 s hs hjoin j hj
  have hrho' : max 2 rho1 ≤ rho := le_of_max_le_left hrho
  have hlarge := hrho1 rho (le_of_max_le_right hrho')
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrho'
  have hcr : c < lambda * (rho : ℝ) := c_lt_lambda_mul hlambda (le_of_max_le_right hrho)
  have hNo := noCellInside hlambda hlambda1 hc hmu hmu1 hlarge hrho2 hW hleast hbelow S
  have hvalue := S.cell_listVal_ne_one hW hlambda hcr
  exact main hNo hvalue hmin P h2 hs hjoin hj

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01CellJunctionValue.proof
