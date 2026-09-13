import GroupApproximation.Manuscript.NonMFSentences.NormalKazhdanUltrafilterRoute
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow
import GroupApproximation.Sofic.HilbertSchmidtAdjointGap
import GroupApproximation.Sofic.CliffordWitnessHSRemark
import GroupApproximation.Meta.AxiomGuard

/-!
# The introduction's limiting trace and its footnote

`non_mf_groups_exist.tex`, Introduction, the outline of the proof of
Theorem `thm:compression-criterion` (tex lines 187-205, census row
`61827aea7807`):

> Second, let `K ≤ 𝔇_G(L)` be a normal property-(T) subgroup and let a corona
> homomorphism be nontrivial on `K`.  It compresses to a corner on which the
> Kazhdan projection of `K` vanishes, and the corner, renormalized by its own
> rank, carries an operator norm asymptotic representation to which the first
> step applies.  Its limiting trace is then the trivial character of `K`, which
> takes the value `1` on that projection (Theorem `thm:normal-kazhdan`).

with the footnote

> A Hilbert--Schmidt bound on the multiplicative defect does not give an
> operator norm bound on the conjugation maps, so this argument does not apply
> to sofic or hyperlinear approximations; the sofic group of
> Section `sec:amenable-nonqd` shows that its conclusion fails there.

## What is carried

* `manuscriptSentence_limitingTraceIsTrivialCharacter`: `L` has property (T),
  `K ≤ 𝔇_G(L)` is a normal property-(T) subgroup, `D` is a corner (the corner
  models renormalized by their own rank, with the operator norm asymptotic
  representation `(W_n)`), `π : C*_max(K) → 𝒬_r` is induced by `Θ̂|_K`, and `ω` is
  a free ultrafilter.  The limiting trace `τ = lim_ω tr_{r_n}` satisfies
  `τ ∘ π = χ` on all of `C*_max(K)`, `K` has a Kazhdan projection, and every
  Kazhdan projection `e_K` has `χ(e_K) = 1 = τ(π(e_K))`.  The first step
  applies through Corollary `cor:defect-hs` in radical form
  (`printedDefect_le_opToHSShadowResidual_direct`), and the trace sentences are
  those of `NormalKazhdanUltrafilterRoute.lean`.
* `manuscriptSentence_compressionOutlineFootnote`, three clauses.
  (1) Unitaries arbitrarily close in normalized Hilbert--Schmidt norm have
  conjugation maps `Ad U = U ⊗ Ū` (`conjDouble`) at operator norm distance `2`,
  and no modulus bounds the operator norm distance of the conjugation maps by
  the Hilbert--Schmidt distance (`HilbertSchmidtAdjointGap.lean`).  The
  multiplicative defect `V(gh) - V(g)V(h)` is such a difference.
  (2) The sofic group `W` of Section `sec:amenable-nonqd`, with `L` the level-zero
  copy of `Γ̄` and `K = ⟨ε⟩`, satisfies the hypotheses, and the first step fails
  there: `W` has a unitary Hilbert--Schmidt asymptotic representation that does
  not send `ε` to `1`.
  (3) The sofic and hyperlinear versions of the conclusion are false under the
  hypotheses (`CliffordWitnessHSRemark.lean`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open OneSidedMFRadical
open OneSidedMFRadical.NormalKazhdanPrintedRoute
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Printed sentence** (tex 199-201): "Its limiting trace is then the trivial
character of `K`, which takes the value `1` on that projection
(Theorem `thm:normal-kazhdan`)."

For a property-(T) subgroup `L`, a normal property-(T) subgroup `K ≤ 𝔇_G(L)`, a
corner `D`, the homomorphism `π` induced by `Θ̂|_K`, and a free ultrafilter `ω`:
the limiting trace composed with `π` is the trivial character `χ` of `K`, `K` has a
Kazhdan projection, and `χ` and the limiting trace take the value `1` on every
Kazhdan projection of `K`. -/
def PrintedLimitingTraceIsTrivialCharacter : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G), HasKazhdanPropertyT.{0, 0} ↥L →
    ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K → K ≤ printedDefect L →
      ∀ (model : ℕ → FiniteModel) (D : PrintedCornerData G model)
        (π : MaximalGroupCStar ↥K →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ D.cornerModel n)),
        (∀ k : ↥K, π (maximalGroupCStarGenerator ↥K k)
          = ((cornerCoronaUnitaryHom D (k : G) :
              unitary (NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) :
                NormMatrixCStarCorona (fun n ↦ D.cornerModel n))) →
        ∀ (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite),
          (∀ x : MaximalGroupCStar ↥K,
            ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω (π x)
              = maximalGroupCStarTrivialCharacter ↥K x) ∧
          Nonempty (KazhdanData ↥K) ∧
          ∀ KD : KazhdanData ↥K,
            maximalGroupCStarTrivialCharacter ↥K KD.projection = 1 ∧
              ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω
                (π KD.projection) = 1

theorem manuscriptSentence_limitingTraceIsTrivialCharacter :
    PrintedLimitingTraceIsTrivialCharacter := by
  intro _ _ _ L hL K _ hT hKD _ D π hπ ω hω
  have hτπ := manuscriptSentence_ultrafilterTraceOfInducedGeneratorIsOne K.subtype
    (fun s ↦ printedDefect_le_opToHSShadowResidual_direct L hL (hKD s.2)) D ω hω π hπ
  obtain ⟨-, -, hagree⟩ := manuscriptSentence_statesAgreeOnGeneratorsSpanAndAlgebra π
    (ultrafilterNormalizedTraceCLM (fun n ↦ D.cornerModel n) ω hω) hτπ
  refine ⟨hagree, exists_kazhdanData ↥K hT, fun KD ↦ ?_⟩
  obtain ⟨-, -, -, hχe⟩ := manuscriptSentence_trivialCharacterIsStateWithValues KD
  exact ⟨hχe, (hagree KD.projection).trans hχe⟩

/-- **Printed footnote** (tex 201-205): "A Hilbert--Schmidt bound on the
multiplicative defect does not give an operator norm bound on the conjugation
maps, so this argument does not apply to sofic or hyperlinear approximations; the
sofic group of Section `sec:amenable-nonqd` shows that its conclusion fails
there."

(1) Hilbert--Schmidt closeness of unitaries gives no operator norm bound on the
difference of their conjugation maps `conjDouble U = U ⊗ Ū`.  (2) The sofic group
`W = LiteralNonMFLinearWitness.WitnessGroup`, with `L` the level-zero copy of `Γ̄`
and `K` the sign subgroup `⟨ε⟩`, satisfies the hypotheses (`L` and `K` have
property (T), `K ≤ 𝔇_W(L)`, `ε ≠ 1`), while a unitary Hilbert--Schmidt asymptotic
representation of `W` does not send `ε` to `1`.  (3) The conclusion fails for sofic
and hyperlinear approximations: under the hypotheses the group can be sofic, it
can be hyperlinear, and a homomorphism to a sofic group need not kill `K`. -/
def PrintedCompressionOutlineFootnote : Prop :=
  ((∀ ε : ℝ, 0 < ε → ∃ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
      U ∈ Matrix.unitaryGroup Y ℂ ∧ V ∈ Matrix.unitaryGroup Y ℂ ∧
        Real.sqrt (hsNormSq Y (U - V)) ≤ ε ∧
        2 ≤ ‖conjDouble U - conjDouble V‖) ∧
    ¬ ∃ m : ℝ → ℝ,
      Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
        U ∈ Matrix.unitaryGroup Y ℂ → V ∈ Matrix.unitaryGroup Y ℂ →
          ∀ δ : ℝ, 0 < δ → Real.sqrt (hsNormSq Y (U - V)) ≤ δ →
            ‖conjDouble U - conjDouble V‖ ≤ m δ) ∧
  (IsSofic LiteralNonMFLinearWitness.WitnessGroup ∧
    HasKazhdanPropertyT.{0, 0} ↥(CliffordWitnessDirectDefect.baseSubgroup
      LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective) ∧
    HasKazhdanPropertyT.{0, 0} ↥(CliffordWitnessDirectDefect.signSubgroup
      LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective) ∧
    CliffordWitnessDirectDefect.signSubgroup LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective ≤
      printedDefect (CliffordWitnessDirectDefect.baseSubgroup
        LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective) ∧
    CliffordWitnessHSRemark.witnessSign ∈ CliffordWitnessDirectDefect.signSubgroup
      LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective ∧
    CliffordWitnessHSRemark.witnessSign ≠ 1 ∧
    ∃ (d : ℕ → FiniteModel)
      (V : (n : ℕ) → LiteralNonMFLinearWitness.WitnessGroup → Matrix (d n) (d n) ℂ),
      (∀ n g, V n g ∈ Matrix.unitaryGroup (d n) ℂ) ∧
      (∀ g h : LiteralNonMFLinearWitness.WitnessGroup,
        Tendsto (fun n ↦ hsNorm (d n) (V n (g * h) - V n g * V n h)) atTop (𝓝 0)) ∧
      ¬ Tendsto (fun n ↦ hsNorm (d n) (V n CliffordWitnessHSRemark.witnessSign - 1))
        atTop (𝓝 0)) ∧
  (¬ (∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
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
              f k = 1))

theorem manuscriptSentence_compressionOutlineFootnote :
    PrintedCompressionOutlineFootnote := by
  obtain ⟨hmodels, -, -, hne, -⟩ := CliffordWitnessHSRemark.manuscriptSentence_hsCollapseFails
  exact ⟨⟨HilbertSchmidtAdjointGap.exists_hsClose_adjointFar,
      HilbertSchmidtAdjointGap.no_vanishing_modulus_controls_adjoint⟩,
    ⟨LiteralWitnessConsequences.witnessGroup_isSofic,
      CliffordWitnessDirectDefect.baseSubgroup_hasKazhdanPropertyT
        LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective
        CommutingLampCollapse.gammaBar_hasKazhdanPropertyT,
      hasKazhdanPropertyT_of_finite ↥(CliffordWitnessDirectDefect.signSubgroup
        LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective),
      CliffordWitnessDirectDefect.signSubgroup_le_printedDefect
        LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective
        AmenableTraceTheorem.manuscriptAffineCliffordHypotheses.2,
      CliffordWitnessHSRemark.witnessSign_mem_signSubgroup, hne, hmodels⟩,
    CliffordWitnessHSRemark.manuscriptSentence_noSoficCompressionCriterion⟩

end

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_limitingTraceIsTrivialCharacter
#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_compressionOutlineFootnote
