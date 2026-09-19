import GroupApproximation.GGT.DGOProposition414GeneralFinite
import GroupApproximation.GGT.DGOProposition414GeneralChildren
import GroupApproximation.GGT.DGOProposition414SuppliedRadii
import GroupApproximation.GGT.DGOProposition414LinearSumBound

/-!
# The genuine child-cost inequality for DGO's balanced surgery

Choose relative-radius witnesses from the general least-cost function on
each actual auxiliary child. The existing geometric factor placement charges
those witnesses without overlap, producing the original polygon's witness.
-/

namespace GroupApproximation.GGT.DGOProposition414

open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- Distributed factors are bounded by the sum of the genuine child costs. -/
theorem TwoHalfDistributedFactorPlacement.exists_witness_of_quasiCosts
    {D : RelGenSet G Λ}
    {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base} {δ b : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D (b : ℝ) index}
    {I : Finset ℕ} {lam : ℕ → Λ} {span : ℕ → G}
    (E : TwoHalfDistributedFactorPlacement D hsymm b hδ A I lam span)
    (mu : ℝ) (err : ℕ) (hmu : 1 ≤ mu)
    (hfirst : ∀ j, (A.firstChildren j).QuasiAt mu (err : ℝ))
    (hsecond : ∀ j, (A.secondChildren j).QuasiAt mu (err : ℝ)) :
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I, span s ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤
        (∑ j, quasiSumCost D hsymm mu err hmu hδ (A.firstSides j)) +
          ∑ j, quasiSumCost D hsymm mu err hmu hδ (A.secondSides j) := by
  classical
  have hf := fun j => quasiSumBound_quasiSumCost D hsymm mu err hmu hδ
    (A.firstSides j) ((A.firstChildren j).atParameters (hfirst j))
  have hs := fun j => quasiSumBound_quasiSumCost D hsymm mu err hmu hδ
    (A.secondSides j) ((A.secondChildren j).atParameters (hsecond j))
  choose rf hrf hsumf using hf
  choose rs hrs hsums using hs
  let rho := Sum.elim rf rs
  have hrho : ∀ q t, t ∈ twoHalfChildTarget A q →
      twoHalfChildSpan A q t ∈ D.relBall (twoHalfChildLabel A q t) (rho q t) := by
    intro q t ht
    cases q with
    | inl j => exact hrf j t ht
    | inr j => exact hrs j t ht
  obtain ⟨r, hr, hsum⟩ := E.exists_witness_of_suppliedRadii rho hrho
  refine ⟨r, hr, hsum.trans ?_⟩
  rw [Fintype.sum_sum_type]
  exact Nat.add_le_add (Finset.sum_le_sum (fun j _ => hsumf j))
    (Finset.sum_le_sum (fun j _ => hsums j))

/-- Complete canonical surgery exists on the same combinatorial split. -/
theorem BalancedSplitData.exists_gapCompletion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ}
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    {P : SumBoundInput D (b : ℝ) n}
    (B : BalancedSplitData D hsymm b hδ P k R) :
    Nonempty (BalancedSplitGapCompletion D hsymm b hδ P B) := by
  obtain ⟨⟨first⟩, ⟨second⟩⟩ := B.exists_gapComponentFamilies
  exact ⟨B.gapCompletion_of_certificates
    (first.toCertificate B.firstGapTargetSeparation)
    (second.toCertificate B.secondGapTargetSeparation)⟩

/-- A general input is paid for by the genuine costs of its actual children. -/
theorem QuasiSumBoundInput.hasRadiusWitness_of_gapCompletion
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {δ b n k R : ℕ} {mu : ℝ} (hmu : 1 ≤ mu)
    {hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ}
    (P : QuasiSumBoundInput D mu (b : ℝ) n)
    (B : BalancedSplitData D hsymm P.word.length hδ P.bookkeeping k R)
    (S : BalancedSplitGapCompletion D hsymm P.word.length hδ P.bookkeeping B) :
    P.HasRadiusWitnessAtMost
      ((∑ j, quasiSumCost D hsymm mu b hmu hδ
        (((B.gapIntervalsOfConfigurations S.components).toPathInput).first j).sideCount) +
      ∑ j, quasiSumCost D hsymm mu b hmu hδ
        (((B.gapIntervalsOfConfigurations S.components).toPathInput).second j).sideCount) := by
  exact S.factorGeometry.exists_witness_of_quasiCosts mu b hmu
    (B.firstGapChild_quasi_at S.components mu b hmu (Nat.cast_nonneg b) P.quasi)
    (B.secondGapChild_quasi_at S.components mu b hmu (Nat.cast_nonneg b) P.quasi)

end GroupApproximation.GGT.DGOProposition414

#audit_axioms GroupApproximation.GGT.DGOProposition414.TwoHalfDistributedFactorPlacement.exists_witness_of_quasiCosts
#audit_axioms GroupApproximation.GGT.DGOProposition414.BalancedSplitData.exists_gapCompletion
#audit_axioms GroupApproximation.GGT.DGOProposition414.QuasiSumBoundInput.hasRadiusWitness_of_gapCompletion
