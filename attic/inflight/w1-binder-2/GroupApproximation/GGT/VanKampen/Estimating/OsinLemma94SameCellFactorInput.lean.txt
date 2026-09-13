import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonCount
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the same-cell unbound darts by a factor, from the scan along each cell

Osin (math/0411039v3, §9), proof of Lemma 9.4.  An unbound dart of a relator cell whose reverse
lies on the same cell lies across no polygon side.  Along the cell word, the pockets behind such
edges have value one (the pocket value clause `OsinLemma94SameCellPocketInput`), so the scan of
`OsinUnboundSameCellScanBound` gives, on each cell `i`,
`λ · #same_i ≤ (1 - λ) · #other_i + c · (1 + runs_i)`, where `runs_i` counts the maximal runs of
bound darts after the first position.  A selected region meets the cells along at most two arcs,
so the runs number at most `2 |M|` in total.

* `OsinLemma94SameCellScanInput`: that scan, at the parameters of Lemma 9.4 with clause (b) of
  Lemma 9.7 below the number of relator cells in scope.  It is the dart instantiation of
  `OsinUnboundSameCellScanBound`, stated as a named residual.
* `OsinLemma94SameCellFactorInput`: hypothesis (ii) of
  `OsinLemma94ClassPolygons.classCovers_of_sameCellFactor`, with `M₀ = ⌈1/λ⌉₊` and
  `T = 25 ⌈c/λ⌉₊`.
* `OsinLemma94SameCellFactor.le_ceil_mul_add` and `sum_le_ceil_mul_add`: the counting step.
  From `λ X ≤ (1 - λ) N + c s` it gives `X ≤ ⌈1/λ⌉₊ N + ⌈c/λ⌉₊ s`, and it sums over the cells.
* `osinLemma94SameCellFactorInput_of_scan`: (ii) from the scan, using `|M| ≤ 12 n`.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.  The scan is a residual: this module reshapes (ii) over
it and discharges nothing below it.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open scoped Classical

namespace OsinLemma94SameCellFactor

/-- **The counting step on one cell.**  If `λ X ≤ (1 - λ) N + c s` with `λ > 0`, `N ≥ 0` and
`s ≥ 0`, then `X ≤ ⌈1/λ⌉₊ N + ⌈c/λ⌉₊ s`. -/
theorem le_ceil_mul_add {lambda c X N s : ℝ} (hlam : 0 < lambda) (hN : 0 ≤ N) (hs : 0 ≤ s)
    (h : lambda * X ≤ (1 - lambda) * N + c * s) :
    X ≤ (⌈1 / lambda⌉₊ : ℝ) * N + (⌈c / lambda⌉₊ : ℝ) * s := by
  have h1 : 1 / lambda ≤ (⌈1 / lambda⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : c / lambda ≤ (⌈c / lambda⌉₊ : ℝ) := Nat.le_ceil _
  have e : 1 / lambda * N + c / lambda * s = (N + c * s) / lambda := by ring
  have hX : X ≤ 1 / lambda * N + c / lambda * s := by
    rw [e, le_div_iff₀ hlam]
    nlinarith [mul_nonneg hlam.le hN]
  nlinarith [mul_le_mul_of_nonneg_right h1 hN, mul_le_mul_of_nonneg_right h2 hs]

/-- **The counting step, summed.**  If on each index `λ X_i ≤ (1 - λ) N_i + c (1 + runs_i)`,
there are at most `n` indices and at most `R` runs in total, then
`∑ X_i ≤ ⌈1/λ⌉₊ ∑ N_i + ⌈c/λ⌉₊ (n + R)`. -/
theorem sum_le_ceil_mul_add {ι : Type*} [Fintype ι] {lambda c : ℝ} (hlam : 0 < lambda)
    (X N runs : ι → ℕ) {n R : ℕ} (hcard : Fintype.card ι ≤ n) (hruns : ∑ i, runs i ≤ R)
    (h : ∀ i, lambda * (X i : ℝ) ≤ (1 - lambda) * (N i : ℝ) + c * (1 + (runs i : ℝ))) :
    (∑ i, (X i : ℝ)) ≤
      (⌈1 / lambda⌉₊ : ℝ) * ∑ i, (N i : ℝ) + (⌈c / lambda⌉₊ : ℝ) * ((n : ℝ) + (R : ℝ)) := by
  have hstep : ∀ i, (X i : ℝ) ≤
      (⌈1 / lambda⌉₊ : ℝ) * (N i : ℝ) + (⌈c / lambda⌉₊ : ℝ) * (1 + (runs i : ℝ)) :=
    fun i => le_ceil_mul_add hlam (Nat.cast_nonneg _) (by positivity) (h i)
  have hs : (∑ i, (1 + (runs i : ℝ))) ≤ (n : ℝ) + (R : ℝ) := by
    rw [Finset.sum_add_distrib]
    have h1 : ((Fintype.card ι : ℕ) : ℝ) ≤ n := by exact_mod_cast hcard
    have h2 : (∑ i, (runs i : ℝ)) ≤ R := by exact_mod_cast hruns
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    linarith
  calc (∑ i, (X i : ℝ))
      ≤ ∑ i, ((⌈1 / lambda⌉₊ : ℝ) * (N i : ℝ) + (⌈c / lambda⌉₊ : ℝ) * (1 + (runs i : ℝ))) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (⌈1 / lambda⌉₊ : ℝ) * ∑ i, (N i : ℝ) +
          (⌈c / lambda⌉₊ : ℝ) * ∑ i, (1 + (runs i : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (⌈1 / lambda⌉₊ : ℝ) * ∑ i, (N i : ℝ) + (⌈c / lambda⌉₊ : ℝ) * ((n : ℝ) + (R : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) ⌈c / lambda⌉₊)
        linarith

end OsinLemma94SameCellFactor

/-- **The scan along each cell (residual).**  At the parameters of Lemma 9.4, for `ρ` large,
with clause (b) of Lemma 9.7 below the number of relator cells of `Δ` in scope: for every
distinguished system there are run counts with at most `2 |M|` runs in total such that on each
relator cell `i`, `λ · #same_i ≤ (1 - λ) · #other_i + c · (1 + runs_i)`.  Here `same_i` are the
unbound darts of cell `i` with cell `i` across and `other_i` the other unbound darts of cell `i`.
This is `OsinUnboundSameCellScanBound` on each cell word, with the pockets of value one from
`OsinLemma94SameCellPocketInput`. -/
def OsinLemma94SameCellScanInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ eps : ℕ,
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
                  ∃ runs : Fin S.diagram.rCellCount → ℕ, ∑ i, runs i ≤ 2 * S.family.card ∧
                    ∀ i : Fin S.diagram.rCellCount,
                      lambda * (((RegionCandidate.unboundDarts S.family i).filter fun d =>
                          (cell S.diagram i).face =
                            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ) ≤
                        (1 - lambda) * (((RegionCandidate.unboundDarts S.family i).filter fun d =>
                          ¬ (cell S.diagram i).face =
                            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ) +
                          c * (1 + (runs i : ℝ))

/-- **Hypothesis (ii) of the same-cell factor cover.**  At the parameters of Lemma 9.4, for `ρ`
large, with clause (b) of Lemma 9.7 below the number of relator cells in scope, the unbound darts
with their own cell across number at most `⌈1/λ⌉₊` times the other unbound darts plus
`25 ⌈c/λ⌉₊ n`. -/
def OsinLemma94SameCellFactorInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ eps : ℕ,
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
                  (∑ i : Fin S.diagram.rCellCount,
                      (((RegionCandidate.unboundDarts S.family i).filter fun d =>
                        (cell S.diagram i).face =
                          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
                    ((⌈1 / lambda⌉₊ : ℕ) : ℝ) * (∑ i : Fin S.diagram.rCellCount,
                      (((RegionCandidate.unboundDarts S.family i).filter fun d =>
                        ¬ (cell S.diagram i).face =
                          S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) +
                      ((25 * ⌈c / lambda⌉₊ : ℕ) : ℝ) * Delta.rCellCount

/-- **Hypothesis (ii) from the scan along each cell.**  Sum the counting step over the relator
cells; there are `n` of them, and at most `2 |M| ≤ 24 n` runs. -/
theorem osinLemma94SameCellFactorInput_of_scan
    (hscan : OsinLemma94SameCellScanInput.{u, w, v}) :
    OsinLemma94SameCellFactorInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  obtain ⟨rho0, hrho0, hK⟩ := hscan D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16 eps
  refine ⟨rho0, hrho0, fun rho hrho W hW Delta cuts hleast hcells hbelow S hcard hmin => ?_⟩
  obtain ⟨runs, hruns, hcell⟩ := hK rho hrho W hW Delta cuts hleast hcells hbelow S hcard hmin
  have hfam : S.family.card ≤ 12 * Delta.rCellCount := by
    have := cuts.count_le
    omega
  have e : S.diagram.rCellCount = Delta.rCellCount := by
    simpa using (Fintype.card_congr S.equiv.cellIndex).symm
  have key : (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
      (⌈1 / lambda⌉₊ : ℝ) * (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) +
        (⌈c / lambda⌉₊ : ℝ) * ((Delta.rCellCount : ℝ) + ((24 * Delta.rCellCount : ℕ) : ℝ)) :=
    OsinLemma94SameCellFactor.sum_le_ceil_mul_add hlambda
      (fun i => ((RegionCandidate.unboundDarts S.family i).filter fun d =>
          (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card)
      (fun i => ((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card)
      runs ((Fintype.card_fin _).trans_le e.le) (hruns.trans (by omega)) hcell
  push_cast at key ⊢
  linarith

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94SameCellFactor.le_ceil_mul_add
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94SameCellFactor.sum_le_ceil_mul_add
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94SameCellFactorInput_of_scan

end GroupApproximation.GGT.VanKampen
