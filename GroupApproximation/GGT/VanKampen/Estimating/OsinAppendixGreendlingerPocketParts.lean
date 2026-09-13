import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixGreendlingerParts
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLemma97Pocket
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist of Osin's Lemma 4.4 from the pocket parts

`Estimating/OsinAppendixGreendlingerParts` proves the least-area Greendlinger waist of Osin's
Lemma 4.4 (arXiv:math/0411039v3) from Lemma 9.4 and four uniform parts, one per input of
Lemma 9.7.  `Estimating/OsinAppendixLemma97Pocket` replaces the Euler clause by the Euler count
of `Φ'_M` (`PhiPrimeCountInput`) and the descent clause by the section pocket producer
(`SectionPocketCutInput`).  This module states those two producers uniformly, with the same
quantifier prefix, and assembles the waist from them.

## What is proved here

* `OsinPhiPrimeCountSectionStatement` and `OsinSectionPocketCutSectionStatement`: the two
  producers, uniformly in the parameters;
* `osinEulerCountSection_of_phiPrimeCount`: the Euler part from the count of `Φ'_M`;
* `osinSection97PocketInputs_of_parts`: `OsinSection97PocketInputsStatement` from the cut parts
  and the two producers, the thresholds combined by maxima;
* `osinDescentSection_of_pocketParts`: the descent part from Lemma 9.4, the cut parts and the
  two producers;
* `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts`: the waist of Lemma 4.4 from
  Lemma 9.4, the cut parts and the two producers.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-! ## The two producers -/

/-- **G3, uniformly in the parameters**: the Euler count of `Φ'_M`, `PhiPrimeCountInput`, for
every symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large. -/
def OsinPhiPrimeCountSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              PhiPrimeCountInput.{u, w, v} D lambda c eps W

/-- **The section pocket producer, uniformly in the parameters**: `SectionPocketCutInput` for
every symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large. -/
def OsinSectionPocketCutSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              SectionPocketCutInput.{u, w, v} D lambda c eps W

/-! ## The assembly -/

/-- **The Euler part from the count of `Φ'_M`**, at the same thresholds, through
`eulerCountInput_of_phiPrimeCount`. -/
theorem osinEulerCountSection_of_phiPrimeCount
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v}) :
    OsinEulerCountSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hcountEps⟩ :=
    hcount D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hcountRho⟩ := hcountEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition =>
    eulerCountInput_of_phiPrimeCount (hcountRho rho hrho W hcondition)⟩

/-- **The pocket inputs of Lemma 9.7 from the cut parts and the two producers.**  `ε₀` is the
largest of the four `ε₀`; at every `ε ≥ ε₀`, `ρ₀` is the largest of the four `ρ₀`, positive
because the first is. -/
theorem osinSection97PocketInputs_of_parts
    (hmulti : OsinMultipleEdgeCutSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hpocket : OsinSectionPocketCutSectionStatement.{u, w, v}) :
    OsinSection97PocketInputsStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsM, hM⟩ := hmulti D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsL, hL⟩ := hloop D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsC, hC⟩ := hcount D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsP, hP⟩ := hpocket D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max (max epsM epsL) (max epsC epsP), fun eps heps => ?_⟩
  obtain ⟨hepsML, hepsCP⟩ := max_le_iff.mp heps
  obtain ⟨hepsM, hepsL⟩ := max_le_iff.mp hepsML
  obtain ⟨hepsC, hepsP⟩ := max_le_iff.mp hepsCP
  obtain ⟨rhoM, hrhoMpos, hMrho⟩ := hM eps hepsM
  obtain ⟨rhoL, -, hLrho⟩ := hL eps hepsL
  obtain ⟨rhoC, -, hCrho⟩ := hC eps hepsC
  obtain ⟨rhoP, -, hPrho⟩ := hP eps hepsP
  refine ⟨max (max rhoM rhoL) (max rhoC rhoP),
    lt_of_lt_of_le hrhoMpos (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrhoML, hrhoCP⟩ := max_le_iff.mp hrho
  obtain ⟨hrhoM, hrhoL⟩ := max_le_iff.mp hrhoML
  obtain ⟨hrhoC, hrhoP⟩ := max_le_iff.mp hrhoCP
  exact ⟨hMrho rho hrhoM W hcondition, hLrho rho hrhoL W hcondition,
    hCrho rho hrhoC W hcondition, hPrho rho hrhoP W hcondition⟩

/-- **The descent part from Lemma 9.4, the cut parts and the two producers**: the descent
clause of `osinSection97Inputs_of_pocketInputs`, with O52 discharged by
`Embedded.o52LeastArea`. -/
theorem osinDescentSection_of_pocketParts
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hmulti : OsinMultipleEdgeCutSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hpocket : OsinSectionPocketCutSectionStatement.{u, w, v}) :
    OsinDescentSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hinEps⟩ := osinSection97Inputs_of_pocketInputs o52LeastArea h94
    (osinSection97PocketInputs_of_parts hmulti hloop hcount hpocket)
    D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hinRho⟩ := hinEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition => (hinRho rho hrho W hcondition).2.2.2⟩

/-- **Osin's Lemma 4.4 at least-area diagrams, from Lemma 9.4, the cut parts and the two
producers**: the Greendlinger waist, through `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hmulti : OsinMultipleEdgeCutSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (hcount : OsinPhiPrimeCountSectionStatement.{u, w, v})
    (hpocket : OsinSectionPocketCutSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs h94
    (osinSection97PocketInputs_of_parts hmulti hloop hcount hpocket)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinPhiPrimeCountSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinSectionPocketCutSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinEulerCountSection_of_phiPrimeCount
#audit_axioms GroupApproximation.GGT.VanKampen.osinSection97PocketInputs_of_parts
#audit_axioms GroupApproximation.GGT.VanKampen.osinDescentSection_of_pocketParts
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts
