import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSmallFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerPocketParts
import GroupApproximation.Meta.AxiomGuard

/-!
# The Euler count of `Φ'_M` uniformly in the parameters, from C4 and C6′

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3: "By (∗), every region of it (except
possibly for the outer one) has degree at least three. Hence f ≤ 2e/3+1."

`Estimating/OsinAppendixEulerSmallFaces` proves `PhiPrimeCountInput` from three pieces: C4
`CornerTwoGonInput`, C5 `CellFaceCountInput` and C6′ `TwoGonHoldsInput`.  C5 is proved
(`cellFaceCountInput`).  This module states C4 and C6′ uniformly in the parameters, with the
quantifier prefix of `OsinPhiPrimeCountSectionStatement`, and assembles that statement from them.

* `OsinCornerTwoGonSectionStatement`: C4, uniformly in the parameters (lane `leavitt-units`).
* `OsinTwoGonHoldsSectionStatement`: C6′, uniformly in the parameters (lane `debt-conditional`).
* `osinPhiPrimeCountSection_of_pieces`: `OsinPhiPrimeCountSectionStatement` from the two, through
  `phiPrimeCountInput_of_smallFaces` with C5 given by `cellFaceCountInput`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-- **C4 of Lemma 9.3, uniformly in the parameters** (lane `leavitt-units`): `CornerTwoGonInput`
for every symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large, with
the quantifier prefix of `OsinPhiPrimeCountSectionStatement`. -/
def OsinCornerTwoGonSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CornerTwoGonInput.{u, w, v} D lambda c eps W

/-- **C6′ of Lemma 9.3, uniformly in the parameters** (lane `debt-conditional`):
`TwoGonHoldsInput` for every symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then
`ρ` are large, with the quantifier prefix of `OsinPhiPrimeCountSectionStatement`. -/
def OsinTwoGonHoldsSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              TwoGonHoldsInput.{u, w, v} D lambda c eps W

/-- **G3, the Euler count of `Φ'_M`, uniformly in the parameters, from C4 and C6′.**  `ε₀` is
the larger of the two `ε₀`.  At every `ε ≥ ε₀`, `ρ₀` is the larger of the two `ρ₀`, positive
because the first is.  C5 is `cellFaceCountInput`. -/
theorem osinPhiPrimeCountSection_of_pieces
    (hcorner : OsinCornerTwoGonSectionStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v}) :
    OsinPhiPrimeCountSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsK, hK⟩ := hcorner D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsT, hT⟩ := htwogon D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max epsK epsT, fun eps heps => ?_⟩
  obtain ⟨hepsK, hepsT⟩ := max_le_iff.mp heps
  obtain ⟨rhoK, hrhoKpos, hKrho⟩ := hK eps hepsK
  obtain ⟨rhoT, -, hTrho⟩ := hT eps hepsT
  refine ⟨max rhoK rhoT, lt_of_lt_of_le hrhoKpos (le_max_left _ _),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrhoK, hrhoT⟩ := max_le_iff.mp hrho
  exact phiPrimeCountInput_of_smallFaces (hKrho rho hrhoK W hcondition)
    (cellFaceCountInput D eps W) (hTrho rho hrhoT W hcondition)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinCornerTwoGonSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinTwoGonHoldsSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinPhiPrimeCountSection_of_pieces
