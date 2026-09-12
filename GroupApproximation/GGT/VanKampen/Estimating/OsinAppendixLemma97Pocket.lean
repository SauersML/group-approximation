import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixDescentInduction
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7 and Lemma 4.4 from the section pocket inputs

`Estimating/OsinAppendixAssembly` proves Osin's Lemma 9.7 (arXiv:math/0411039v3) and the
Greendlinger waist of Lemma 4.4 from O52, Lemma 9.4 and `OsinSection97InputsStatement`,
whose descent clause is `DescentInput`.  `Estimating/OsinAppendixDescentInduction`
proves `DescentInput` from the section pocket producer `SectionPocketCutInput`.  This
module replaces the descent clause by the pocket producer, and discharges O52 by
`Embedded.o52LeastArea`.

## What is proved here

* `OsinSection97PocketInputsStatement`: the multiple-edge and loop cut producers, the
  Euler count, and the section pocket producer, with the quantifier prefix of
  `OsinSection97InputsStatement`;
* `osinSection97Inputs_of_pocketInputs`: the inputs with `DescentInput`, from O52,
  Lemma 9.4 and the pocket inputs;
* `osinLemma97Section_of_pocketInputs` and
  `relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs`: Lemma 9.7 and the
  waist of Lemma 4.4 from Lemma 9.4 and the pocket inputs.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-- **The section inputs of Osin's Lemma 9.7, with the pocket producer** (G2, G3–G4,
G6), uniformly in the parameters: the multiple-edge and loop cut producers, the Euler
count of `Φ'_M` with the planar edge bound, and the section pocket producer, for every
symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large. -/
def OsinSection97PocketInputsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgeCutInput.{u, w, v} D lambda c eps W ∧
                LoopCutInput.{u, w, v} D lambda c eps W ∧
                  EulerCountInput.{u, w, v} D lambda c eps W ∧
                    SectionPocketCutInput.{u, w, v} D lambda c eps W

/-- **The descent clause from the pocket producer.**  The thresholds combine by maxima;
at every admissible `ρ`, `descentInput_of_sectionPocketCut` applies, with Lemma 9.4's
conclusion as its `UnboundInput`. -/
theorem osinSection97Inputs_of_pocketInputs
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97PocketInputsStatement.{u, w, v}) :
    OsinSection97InputsStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps94, h94eps⟩ := h94 D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsIn, hinEps⟩ := hin D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max eps94 epsIn, fun eps heps => ?_⟩
  obtain ⟨rho94, hrho94pos, h94rho⟩ := h94eps eps (le_trans (le_max_left _ _) heps)
  obtain ⟨rhoIn, -, hinRho⟩ := hinEps eps (le_trans (le_max_right _ _) heps)
  obtain ⟨rhoLarge, hLarge⟩ := exists_rho_widthBudget lambda c hmu eps
  obtain ⟨rhoThr, hThr⟩ := exists_rho_muSqrt hmu
  refine ⟨max (max rho94 rhoIn) (max rhoLarge rhoThr),
    lt_of_lt_of_le hrho94pos (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hleft, hright⟩ := max_le_iff.mp hrho
  obtain ⟨h1, h2⟩ := max_le_iff.mp hleft
  obtain ⟨h3, h4⟩ := max_le_iff.mp hright
  obtain ⟨hmulti, hloop, heuler, hpocket⟩ := hinRho rho h2 W hcondition
  have hunbound : UnboundInput.{u, w, v} D lambda c eps rho W :=
    fun Delta cuts hlea hcells S hcard =>
      h94rho rho h1 W hcondition Delta cuts hlea hcells S hcard
  exact ⟨hmulti, hloop, heuler,
    descentInput_of_sectionPocketCut hcondition hlambda hmu hmuUpper
      (lt_of_lt_of_le hrho94pos h1) (hLarge rho h3) (hThr rho h4) hO52 hmulti hloop heuler
      hunbound hpocket⟩

/-- **Osin's Lemma 9.7 at up to four sections, from Lemma 9.4 and the pocket inputs.**
O52 is `Embedded.o52LeastArea`. -/
theorem osinLemma97Section_of_pocketInputs
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97PocketInputsStatement.{u, w, v}) :
    OsinLemma97SectionStatement.{u, w, v} :=
  osinLemma97Section_of_inputs o52LeastArea h94
    (osinSection97Inputs_of_pocketInputs o52LeastArea h94 hin)

/-- **Osin's Lemma 4.4 at least-area diagrams, from Lemma 9.4 and the pocket inputs**:
the Greendlinger waist, through Lemma 9.7 at one section. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97PocketInputsStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97
    (osinLemma97Section_of_pocketInputs h94 hin)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinSection97PocketInputsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinSection97Inputs_of_pocketInputs
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97Section_of_pocketInputs
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_pocketInputs
