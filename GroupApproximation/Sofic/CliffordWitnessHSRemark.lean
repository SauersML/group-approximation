import GroupApproximation.Sofic.SoficPermutationTrace
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.LeavittTraceFloor
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Where operator norm enters: the sofic models of `W`

The remark after Proposition `prop:clifford-locally-rf` in
`non_mf_groups_exist.tex` (Section `sec:amenable-nonqd`):

> Soficity also shows where operator norm enters.  The permutation matrices
> `V_n` of a sofic approximation of `W` satisfy `‖V_n(gh) - V_n(g)V_n(h)‖₂ → 0`,
> while `‖V_n(ε) - 1‖₂ → √2`, because `ε ≠ 1` moves almost every point.  So the
> collapse of Corollary `cor:defect-hs` fails for asymptotic representations in
> normalized Hilbert--Schmidt norm, although `ε` is a central involution of `W`
> inside `𝔇_W(Γ)`: Theorem `thm:transport` needs operator norm control of the
> conjugation maps, and no version of Theorem `thm:compression-criterion` for
> sofic or hyperlinear approximation follows from these hypotheses.

## The mechanism

For permutations the normalized Hilbert--Schmidt distance of the permutation
matrices is twice the Hamming distance (`permMatrix_hsDistSq`).  So along a sofic
approximation `σ_n` with `V_n(g) = permMatrix (σ_n(g)⁻¹)`:

* `‖V_n(gh) - V_n(g)V_n(h)‖₂² = 2 d_H(σ_n(gh), σ_n(g)σ_n(h)) → 0`;
* `‖V_n(ε) - 1‖₂² = 2 d_H(σ_n(ε), 1) → 2`, and `d_H(σ_n(ε), 1)` is exactly the
  fraction of points `σ_n(ε)` moves.

## What is carried

* `manuscriptSentence_soficPermutationModelsHS`: a sofic approximation of `W`
  exists, and every one has the two printed limits and moves almost every point;
* `manuscriptSentence_hsCollapseFails`: the Hilbert--Schmidt analogue of the
  collapse fails at `W` (a unitary Hilbert--Schmidt asymptotic representation
  with `‖V_n(ε) - 1‖₂ ↛ 0`), while `ε` is a central involution in the printed
  intrinsic defect of the level-zero copy of `Γ̄`;
* `manuscriptSentence_noSoficCompressionCriterion`: the sofic and hyperlinear
  versions of the conclusions of `thm:compression-criterion` are false under its
  hypotheses, witnessed by `W` itself.
-/

namespace GroupApproximation
namespace CliffordWitnessHSRemark

open Filter SoficPermutationTrace
open scoped Topology

/-! ## The models of any sofic approximation -/

section Models

variable {G : Type*} [Group G]

/-- The multiplicative defect of the models, in normalized Hilbert--Schmidt
norm, is twice the Hamming defect of the approximation. -/
theorem hsNormSq_modelUnitary_mul (S : SoficApproximation G) (n : ℕ) (g h : G) :
    hsNormSq (S.model n)
        (modelUnitary S n (g * h) - modelUnitary S n g * modelUnitary S n h) =
      2 * hammingDistance (S.model n) (S.map n (g * h)) (S.map n g * S.map n h) := by
  have hhom : modelUnitary S n g * modelUnitary S n h =
      ((S.map n g * S.map n h)⁻¹).permMatrix ℂ := by
    rw [modelUnitary, modelUnitary, _root_.mul_inv_rev, Matrix.permMatrix_mul]
  show hsDistSq (S.model n) (modelUnitary S n (g * h))
      (modelUnitary S n g * modelUnitary S n h) = _
  rw [hhom, modelUnitary, permMatrix_hsDistSq, hammingDistance_inv]

/-- The distance of a model to the identity, in normalized Hilbert--Schmidt
norm, is twice the Hamming distance of the permutation to the identity. -/
theorem hsNormSq_modelUnitary_sub_one (S : SoficApproximation G) (n : ℕ) (g : G) :
    hsNormSq (S.model n) (modelUnitary S n g - 1) =
      2 * hammingDistance (S.model n) (S.map n g) 1 := by
  have h1 : (1 : Matrix (S.model n) (S.model n) ℂ) =
      ((1 : Equiv.Perm (S.model n))⁻¹).permMatrix ℂ := by
    rw [inv_one, Matrix.permMatrix_one]
  show hsDistSq (S.model n) (modelUnitary S n g) 1 = _
  rw [h1, modelUnitary, permMatrix_hsDistSq, hammingDistance_inv]

theorem tendsto_hammingDistance_mul (S : SoficApproximation G) (g h : G) :
    Tendsto (fun n ↦
        hammingDistance (S.model n) (S.map n (g * h)) (S.map n g * S.map n h))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hammingDistance_nonnegative _ _ _)]
  exact hN n hn

theorem tendsto_hammingDistance_one_of_ne_one (S : SoficApproximation G) {g : G}
    (hg : g ≠ 1) :
    Tendsto (fun n ↦ hammingDistance (S.model n) (S.map n g) 1) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := S.asymptoticallyFaithful g hg ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 := hN n hn
  have h2 := hammingDistance_le_one (S.model n) (S.map n g) 1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Asymptotic multiplicativity in normalized Hilbert--Schmidt norm.** -/
theorem tendsto_hsNorm_modelUnitary_mul (S : SoficApproximation G) (g h : G) :
    Tendsto (fun n ↦ hsNorm (S.model n)
        (modelUnitary S n (g * h) - modelUnitary S n g * modelUnitary S n h))
      atTop (𝓝 0) := by
  have h2 := (Real.continuous_sqrt.tendsto _).comp
    ((tendsto_hammingDistance_mul S g h).const_mul 2)
  rw [mul_zero, Real.sqrt_zero] at h2
  refine h2.congr fun n ↦ ?_
  rw [Function.comp_apply, hsNorm, hsNormSq_modelUnitary_mul]

/-- **A nontrivial element stays at distance `√2` from the identity.** -/
theorem tendsto_hsNorm_modelUnitary_sub_one (S : SoficApproximation G) {g : G}
    (hg : g ≠ 1) :
    Tendsto (fun n ↦ hsNorm (S.model n) (modelUnitary S n g - 1)) atTop
      (𝓝 (Real.sqrt 2)) := by
  have h2 := (Real.continuous_sqrt.tendsto _).comp
    ((tendsto_hammingDistance_one_of_ne_one S hg).const_mul 2)
  rw [mul_one] at h2
  refine h2.congr fun n ↦ ?_
  rw [Function.comp_apply, hsNorm, hsNormSq_modelUnitary_sub_one]

/-- **A nontrivial element moves almost every point.** -/
theorem tendsto_movedFraction_of_ne_one (S : SoficApproximation G) {g : G}
    (hg : g ≠ 1) :
    Tendsto (fun n ↦ ((S.map n g).support.card : ℝ) / Fintype.card (S.model n))
      atTop (𝓝 1) := by
  refine (tendsto_hammingDistance_one_of_ne_one S hg).congr fun n ↦ ?_
  rw [hammingDistance_eq_support, inv_one, one_mul]

end Models

/-! ## The witness `W` -/

open ExplicitLinearModel LiteralNonMFLinearWitness MarkedCompression
open CliffordWitnessDirectDefect Manuscript.OneSidedMFRadical

/-- The central involution `ε` of the witness `W`. -/
abbrev witnessSign : WitnessGroup := signAmbient alpha conjD_injective

theorem witnessSign_ne_one : witnessSign ≠ 1 :=
  signAmbient_ne_one alpha conjD_injective

theorem witnessSign_mem_signSubgroup :
    witnessSign ∈ signSubgroup alpha conjD_injective :=
  (mem_centralInvolutionSubgroup_iff _ _ _).mpr (Or.inr rfl)

/-- The sign lies in the printed intrinsic defect of the level-zero copy of `Γ̄`. -/
theorem witnessSign_mem_printedDefect :
    witnessSign ∈ printedDefect (baseSubgroup alpha conjD_injective) :=
  signSubgroup_le_printedDefect alpha conjD_injective
    AmenableTraceTheorem.manuscriptAffineCliffordHypotheses.2
    witnessSign_mem_signSubgroup

/-- **Printed sentence**: "The permutation matrices `V_n` of a sofic
approximation of `W` satisfy `‖V_n(gh) - V_n(g)V_n(h)‖₂ → 0`, while
`‖V_n(ε) - 1‖₂ → √2`, because `ε ≠ 1` moves almost every point."

A sofic approximation of `W` exists, and for every one the models
`V_n(g) = permMatrix (σ_n(g)⁻¹)` are asymptotically multiplicative in normalized
Hilbert--Schmidt norm, `σ_n(ε)` moves almost every point, and
`‖V_n(ε) - 1‖₂ → √2`. -/
theorem manuscriptSentence_soficPermutationModelsHS :
    Nonempty (SoficApproximation WitnessGroup) ∧
      ∀ S : SoficApproximation WitnessGroup,
        (∀ g h : WitnessGroup, Tendsto (fun n ↦ hsNorm (S.model n)
          (modelUnitary S n (g * h) - modelUnitary S n g * modelUnitary S n h))
            atTop (𝓝 0)) ∧
        Tendsto (fun n ↦
            ((S.map n witnessSign).support.card : ℝ) / Fintype.card (S.model n))
          atTop (𝓝 1) ∧
        Tendsto (fun n ↦ hsNorm (S.model n) (modelUnitary S n witnessSign - 1))
          atTop (𝓝 (Real.sqrt 2)) := by
  refine ⟨?_, fun S ↦ ⟨fun g h ↦ tendsto_hsNorm_modelUnitary_mul S g h,
    tendsto_movedFraction_of_ne_one S witnessSign_ne_one,
    tendsto_hsNorm_modelUnitary_sub_one S witnessSign_ne_one⟩⟩
  obtain ⟨S, -⟩ := SoficEnvelopeExistence.exists_positive_soficApproximation
    LiteralWitnessConsequences.witnessGroup_isSofic
  exact ⟨S⟩

/-- **Printed sentence**: "So the collapse of Corollary `cor:defect-hs` fails for
asymptotic representations in normalized Hilbert--Schmidt norm, although `ε` is
a central involution of `W` inside `𝔇_W(Γ)`."

There is a sequence of unitary models of `W` that is asymptotically
multiplicative in normalized Hilbert--Schmidt norm and does not send `ε` to `1`
in that norm, while `ε` is central, an involution, nontrivial, and in the printed
intrinsic defect of the level-zero copy of `Γ̄`.  (Theorem `thm:transport` and
Corollary `cor:defect-hs` hold for operator norm asymptotic representations; this
is the failure of their Hilbert--Schmidt analogue.) -/
theorem manuscriptSentence_hsCollapseFails :
    (∃ (d : ℕ → FiniteModel) (V : (n : ℕ) → WitnessGroup → Matrix (d n) (d n) ℂ),
        (∀ n g, V n g ∈ Matrix.unitaryGroup (d n) ℂ) ∧
        (∀ g h : WitnessGroup,
          Tendsto (fun n ↦ hsNorm (d n) (V n (g * h) - V n g * V n h)) atTop (𝓝 0)) ∧
        ¬ Tendsto (fun n ↦ hsNorm (d n) (V n witnessSign - 1)) atTop (𝓝 0)) ∧
      (∀ w : WitnessGroup, Commute witnessSign w) ∧ witnessSign ^ 2 = 1 ∧
      witnessSign ≠ 1 ∧
      witnessSign ∈ printedDefect (baseSubgroup alpha conjD_injective) := by
  obtain ⟨⟨S⟩, hS⟩ := manuscriptSentence_soficPermutationModelsHS
  obtain ⟨hmul, -, hsign⟩ := hS S
  refine ⟨⟨S.model, fun n g ↦ modelUnitary S n g,
      fun n g ↦ modelUnitary_mem_unitaryGroup S n g, hmul, fun h0 ↦ ?_⟩,
    signAmbient_central alpha conjD_injective, signAmbient_sq alpha conjD_injective,
    witnessSign_ne_one, witnessSign_mem_printedDefect⟩
  have heq := tendsto_nhds_unique hsign h0
  exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' heq

/-- **Printed sentence (last clause)**: "no version of Theorem
`thm:compression-criterion` for sofic or hyperlinear approximation follows from
these hypotheses."

Under the hypotheses of `thm:compression-criterion` (a countable group, a
property `(T)` subgroup `L`, a normal property `(T)` subgroup `K ≤ 𝔇_G(L)`,
`K ≠ 1`), the group need not fail to be sofic, nor hyperlinear, and a
homomorphism to a sofic group need not kill `K`: `W` with `L` the level-zero copy
of `Γ̄` and `K = ⟨ε⟩` is a counterexample to each. -/
theorem manuscriptSentence_noSoficCompressionCriterion :
    ¬ (∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
        HasKazhdanPropertyT.{0, 0} ↥L →
          ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
            K ≤ printedDefect L → K ≠ ⊥ → ¬ IsSofic G) ∧
      ¬ (∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
        HasKazhdanPropertyT.{0, 0} ↥L →
          ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
            K ≤ printedDefect L → K ≠ ⊥ → ¬ IsHyperlinear G) ∧
      ¬ (∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
        HasKazhdanPropertyT.{0, 0} ↥L →
          ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
            K ≤ printedDefect L →
              ∀ (H : Type) [Group H], IsSofic H → ∀ (f : G →* H) (k : G), k ∈ K →
                f k = 1) := by
  have hL : HasKazhdanPropertyT.{0, 0} ↥(baseSubgroup alpha conjD_injective) :=
    baseSubgroup_hasKazhdanPropertyT alpha conjD_injective
      CommutingLampCollapse.gammaBar_hasKazhdanPropertyT
  have hKT : HasKazhdanPropertyT.{0, 0} ↥(signSubgroup alpha conjD_injective) :=
    hasKazhdanPropertyT_of_finite (signSubgroup alpha conjD_injective)
  have hKle : signSubgroup alpha conjD_injective ≤
      printedDefect (baseSubgroup alpha conjD_injective) :=
    signSubgroup_le_printedDefect alpha conjD_injective
      AmenableTraceTheorem.manuscriptAffineCliffordHypotheses.2
  have hKne : signSubgroup alpha conjD_injective ≠ ⊥ := by
    intro hbot
    have hmem := witnessSign_mem_signSubgroup
    rw [hbot, Subgroup.mem_bot] at hmem
    exact witnessSign_ne_one hmem
  refine ⟨fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact h WitnessGroup (baseSubgroup alpha conjD_injective) hL
      (signSubgroup alpha conjD_injective) hKT hKle hKne
      LiteralWitnessConsequences.witnessGroup_isSofic
  · exact h WitnessGroup (baseSubgroup alpha conjD_injective) hL
      (signSubgroup alpha conjD_injective) hKT hKle hKne
      (isHyperlinear_of_isSofic LiteralWitnessConsequences.witnessGroup_isSofic)
  · exact witnessSign_ne_one (h WitnessGroup (baseSubgroup alpha conjD_injective) hL
      (signSubgroup alpha conjD_injective) hKT hKle WitnessGroup
      LiteralWitnessConsequences.witnessGroup_isSofic (MonoidHom.id _) witnessSign
      witnessSign_mem_signSubgroup)

end CliffordWitnessHSRemark
end GroupApproximation

open GroupApproximation.CliffordWitnessHSRemark

#audit_closed_axioms
  GroupApproximation.CliffordWitnessHSRemark.manuscriptSentence_soficPermutationModelsHS

#audit_closed_axioms
  GroupApproximation.CliffordWitnessHSRemark.manuscriptSentence_hsCollapseFails

#audit_closed_axioms
  GroupApproximation.CliffordWitnessHSRemark.manuscriptSentence_noSoficCompressionCriterion
