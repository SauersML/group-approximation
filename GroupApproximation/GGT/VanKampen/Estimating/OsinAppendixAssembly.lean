import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.7 and Lemma 4.4 from the section inputs, uniformly in the parameters

`Estimating/OsinAppendixSectionInduction` proves Osin's Lemma 9.7
(arXiv:math/0411039v3) at FIXED parameters `(D, λ, c, μ, ε, ρ, W)` from named
inputs.  This module chooses the parameters: it assembles the uniform statement
`OsinLemma97SectionStatement`, and through
`relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97` the Greendlinger
waist `RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, from

* `O52LeastAreaStatement` — O52 at least area (G1);
* `OsinLemma94SectionStatement` — Lemma 9.4, which at fixed parameters is
  literally `UnboundInput` (G5);
* `OsinSection97InputsStatement` — the cut producers (G2), the Euler count (G3,
  G4) and the descent (G6), with Lemma 9.4's parameter prefix.

## The parameter choice

`ε₀` is the larger of the two thresholds of Lemma 9.4 and of the inputs.  For
`ε ≥ ε₀`, `ρ₀` is the largest of

* the `ρ₀` of Lemma 9.4 and the `ρ₀` of the inputs,
* `⌈2 λ⁻¹ (3ε + c) / μ⌉ + 1`, which makes `λ⁻¹ (3ε + c) < (μ/2) ρ`
  (`exists_rho_widthBudget`), and
* `⌈μ⁻²⌉`, which makes `1 ≤ μ √ρ` (`exists_rho_muSqrt`);

every numeric side condition of `osinLemma97_atParameters_of_inputs` holds at
every `ρ ≥ ρ₀`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-! ## The inputs of Lemma 9.7, with Lemma 9.4's parameter prefix -/

/-- **The section inputs of Osin's Lemma 9.7** (G2, G3–G4, G6), uniformly in the
parameters: the multiple-edge and loop cut producers, the Euler count of `Φ'_M`
with the planar edge bound, and the `m(Π)` descent, for every symmetrized family
satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large.  The quantifier
prefix is `OsinLemma94SectionStatement`'s. -/
def OsinSection97InputsStatement : Prop :=
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
                    DescentInput.{u, w, v} D lambda c mu eps W

/-! ## The two numeric thresholds -/

/-- **`ρ` large enough for the width budget**: some `ρ₀` makes
`λ⁻¹ (3ε + c) < (μ/2) ρ` for every `ρ ≥ ρ₀`. -/
theorem exists_rho_widthBudget (lambda c : ℝ) {mu : ℝ} (hmu : 0 < mu) (eps : ℕ) :
    ∃ rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
      lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := by
  set K : ℝ := lambda⁻¹ * (3 * (eps : ℝ) + c)
  refine ⟨⌈2 * K / mu⌉₊ + 1, fun rho hrho => ?_⟩
  have hceil : 2 * K / mu ≤ ((⌈2 * K / mu⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hcast : ((⌈2 * K / mu⌉₊ + 1 : ℕ) : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr hrho
  have hlt : 2 * K / mu < (rho : ℝ) := by
    have h1 : ((⌈2 * K / mu⌉₊ + 1 : ℕ) : ℝ) = ((⌈2 * K / mu⌉₊ : ℕ) : ℝ) + 1 :=
      Nat.cast_succ _
    linarith
  have hmul : 2 * K < (rho : ℝ) * mu := (div_lt_iff₀ hmu).mp hlt
  have heq : mu / 2 * (rho : ℝ) = (rho : ℝ) * mu / 2 := by ring
  rw [heq]
  linarith

/-- **`ρ` large enough for the unbound threshold**: some `ρ₀` makes `1 ≤ μ √ρ`
for every `ρ ≥ ρ₀`. -/
theorem exists_rho_muSqrt {mu : ℝ} (hmu : 0 < mu) :
    ∃ rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho → 1 ≤ mu * Real.sqrt (rho : ℝ) := by
  refine ⟨⌈(1 / mu) ^ 2⌉₊, fun rho hrho => ?_⟩
  have hceil : (1 / mu) ^ 2 ≤ ((⌈(1 / mu) ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hcast : ((⌈(1 / mu) ^ 2⌉₊ : ℕ) : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr hrho
  have hsq : Real.sqrt ((1 / mu) ^ 2) ≤ Real.sqrt (rho : ℝ) :=
    Real.sqrt_le_sqrt (le_trans hceil hcast)
  have hinv : 0 ≤ 1 / mu := le_of_lt (one_div_pos.mpr hmu)
  rw [Real.sqrt_sq hinv] at hsq
  calc (1 : ℝ) = mu * (1 / mu) := (mul_one_div_cancel hmu.ne').symm
    _ ≤ mu * Real.sqrt (rho : ℝ) := mul_le_mul_of_nonneg_left hsq hmu.le

/-! ## The assembly -/

/-- **Osin's Lemma 9.7 at up to four sections, from O52, Lemma 9.4 and the
section inputs.**  The thresholds combine by maxima; at every admissible `ρ` the
induction of `osinLemma97_atParameters_of_inputs` applies, with Lemma 9.4's
conclusion as its `UnboundInput`. -/
theorem osinLemma97Section_of_inputs
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97InputsStatement.{u, w, v}) :
    OsinLemma97SectionStatement.{u, w, v} := by
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
  obtain ⟨hmulti, hloop, heuler, hdescent⟩ := hinRho rho h2 W hcondition
  have hunbound : UnboundInput.{u, w, v} D lambda c eps rho W :=
    fun Delta cuts hlea hcells S hcard =>
      h94rho rho h1 W hcondition Delta cuts hlea hcells S hcard
  exact osinLemma97_atParameters_of_inputs hcondition hlambda hmu hmuUpper
    (lt_of_lt_of_le hrho94pos h1) (hLarge rho h3) (hThr rho h4) hO52 hmulti hloop heuler
    hunbound hdescent

/-- **Osin's Lemma 4.4 at least-area diagrams, from O52, Lemma 9.4 and the
section inputs**: the Greendlinger waist, through Lemma 9.7 at one section. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_inputs
    (hO52 : O52LeastAreaStatement.{u, w, v})
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hin : OsinSection97InputsStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_osinLemma97
    (osinLemma97Section_of_inputs hO52 h94 hin)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinSection97InputsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.exists_rho_widthBudget
#audit_axioms GroupApproximation.GGT.VanKampen.exists_rho_muSqrt
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97Section_of_inputs
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_inputs
