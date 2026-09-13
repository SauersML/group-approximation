import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# The Greendlinger waist of Osin's Lemma 4.4 from its four section parts

`Estimating/OsinAppendixAssembly` proves the least-area Greendlinger waist
`RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (Osin, arXiv:math/0411039v3, Lemma 4.4
through Lemma 9.7) from O52, Lemma 9.4 and `OsinSection97InputsStatement`, the conjunction of
the four fixed-parameter inputs under one quantifier prefix.  This module splits that
conjunction into four statements, one per input, each with its own thresholds, so that each
part is proved on its own:

* `OsinMultipleEdgeCutSectionStatement`: `MultipleEdgeCutInput` (G2, multiple edges);
* `OsinLoopCutSectionStatement`: `LoopCutInput` (G2, loops);
* `OsinEulerCountSectionStatement`: `EulerCountInput` (G3 with G4);
* `OsinDescentSectionStatement`: `DescentInput` (G6).

Each carries the quantifier prefix of `OsinLemma94SectionStatement`: the input holds for every
symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large.  A producer
at fixed parameters under the `C`-condition gives the statement with `ε₀ = 0` and `ρ₀ = 1`.

## What is proved here

* `osinLoopCutSection`: the loop part, vacuous because `RespectsSections` excludes loops;
* `osinSection97Inputs_of_parts`: `OsinSection97InputsStatement` from the four parts, the
  thresholds combined by maxima;
* `osinLemma97Section_of_parts` and `relativeGreendlingerQuasiGeodesicLeastArea_of_parts`:
  Lemma 9.7 and the waist of Lemma 4.4 from Lemma 9.4 and the four parts, with O52 discharged
  by `Embedded.o52LeastArea`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-! ## The four parts -/

/-- **G2, multiple edges, uniformly in the parameters**: `MultipleEdgeCutInput` for every
symmetrized family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large.  The
quantifier prefix is `OsinLemma94SectionStatement`'s. -/
def OsinMultipleEdgeCutSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              MultipleEdgeCutInput.{u, w, v} D lambda c eps W

/-- **G2, loops, uniformly in the parameters**: `LoopCutInput` for every symmetrized family
satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large. -/
def OsinLoopCutSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              LoopCutInput.{u, w, v} D lambda c eps W

/-- **G2, loops, uniformly in the parameters**, closed: `RespectsSections` excludes loops, so
`LoopCutInput` is vacuous (`loopCutInput`). -/
theorem osinLoopCutSection : OsinLoopCutSectionStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu _ _ _ _ _
  exact ⟨0, fun eps _ => ⟨1, Nat.one_pos, fun _ _ W _ => loopCutInput.{u, w, v} D lambda c eps W⟩⟩

/-- **G3 with G4, uniformly in the parameters**: `EulerCountInput` for every symmetrized
family satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large. -/
def OsinEulerCountSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              EulerCountInput.{u, w, v} D lambda c eps W

/-- **G6, uniformly in the parameters**: `DescentInput` for every symmetrized family
satisfying `C(ε, μ, λ, c, ρ)` once `ε` and then `ρ` are large. -/
def OsinDescentSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              DescentInput.{u, w, v} D lambda c mu eps W

/-! ## The assembly -/

/-- **The section inputs of Lemma 9.7 from the four parts.**  `ε₀` is the largest of the four
`ε₀`; at every `ε ≥ ε₀`, `ρ₀` is the largest of the four `ρ₀`, positive because the first is. -/
theorem osinSection97Inputs_of_parts
    (hmulti : OsinMultipleEdgeCutSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (heuler : OsinEulerCountSectionStatement.{u, w, v})
    (hdescent : OsinDescentSectionStatement.{u, w, v}) :
    OsinSection97InputsStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsM, hM⟩ := hmulti D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsL, hL⟩ := hloop D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsE, hE⟩ := heuler D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨epsD, hD⟩ := hdescent D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨max (max epsM epsL) (max epsE epsD), fun eps heps => ?_⟩
  obtain ⟨hepsML, hepsED⟩ := max_le_iff.mp heps
  obtain ⟨hepsM, hepsL⟩ := max_le_iff.mp hepsML
  obtain ⟨hepsE, hepsD⟩ := max_le_iff.mp hepsED
  obtain ⟨rhoM, hrhoMpos, hMrho⟩ := hM eps hepsM
  obtain ⟨rhoL, -, hLrho⟩ := hL eps hepsL
  obtain ⟨rhoE, -, hErho⟩ := hE eps hepsE
  obtain ⟨rhoD, -, hDrho⟩ := hD eps hepsD
  refine ⟨max (max rhoM rhoL) (max rhoE rhoD),
    lt_of_lt_of_le hrhoMpos (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun rho hrho W hcondition => ?_⟩
  obtain ⟨hrhoML, hrhoED⟩ := max_le_iff.mp hrho
  obtain ⟨hrhoM, hrhoL⟩ := max_le_iff.mp hrhoML
  obtain ⟨hrhoE, hrhoD⟩ := max_le_iff.mp hrhoED
  exact ⟨hMrho rho hrhoM W hcondition, hLrho rho hrhoL W hcondition,
    hErho rho hrhoE W hcondition, hDrho rho hrhoD W hcondition⟩

/-- **Osin's Lemma 9.7 at up to four sections, from Lemma 9.4 and the four parts.**  O52 is
`Embedded.o52LeastArea`. -/
theorem osinLemma97Section_of_parts
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hmulti : OsinMultipleEdgeCutSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (heuler : OsinEulerCountSectionStatement.{u, w, v})
    (hdescent : OsinDescentSectionStatement.{u, w, v}) :
    OsinLemma97SectionStatement.{u, w, v} :=
  osinLemma97Section_of_inputs o52LeastArea h94
    (osinSection97Inputs_of_parts hmulti hloop heuler hdescent)

/-- **Osin's Lemma 4.4 at least-area diagrams, from Lemma 9.4 and the four parts**: the
Greendlinger waist, through Lemma 9.7 at one section.  O52 is `Embedded.o52LeastArea`. -/
theorem relativeGreendlingerQuasiGeodesicLeastArea_of_parts
    (h94 : OsinLemma94SectionStatement.{u, w, v})
    (hmulti : OsinMultipleEdgeCutSectionStatement.{u, w, v})
    (hloop : OsinLoopCutSectionStatement.{u, w, v})
    (heuler : OsinEulerCountSectionStatement.{u, w, v})
    (hdescent : OsinDescentSectionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesicLeastArea_of_inputs o52LeastArea h94
    (osinSection97Inputs_of_parts hmulti hloop heuler hdescent)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OsinMultipleEdgeCutSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLoopCutSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinEulerCountSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.OsinDescentSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.osinSection97Inputs_of_parts
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma97Section_of_parts
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesicLeastArea_of_parts
#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLoopCutSection
