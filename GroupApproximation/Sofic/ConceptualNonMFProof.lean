import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful

/-!
# The conceptual proof of the literal non-MF theorem

This file is the short, unconditional facade of the checked proof.  The
quantitative matrix estimates and the exact P13 Hodge computation remain the
verification backend; the declarations exposed here follow the mathematical
spine seen by a reader:

1. `u = [d,a]` is the compression defect, where `d = t c t⁻¹`;
2. the marked central involution is exactly `w = u²`;
3. Kazhdan transport makes every compression defect Hilbert--Schmidt trivial;
4. the negative central corner makes `w` converge to `-1`, contradicting
   `w = u² → 1`;
5. the Clifford model detects `w`, so the literal group is not MF.

There are no hypotheses in the final theorem and no duplicated analytic
argument in this facade.
-/

namespace GroupApproximation
namespace LiteralNonMFEndpoint

open LiteralNonMFPresentation
open ReducedGroupCStarTrace
open scoped commutatorElement

noncomputable section

/-! ## Exact property (T) input, discharged once and for all -/

/-- The literal affine base has property `(T)`: the exact rational P13 Hodge
certificate descends through the checked P13 rotation quotient and the
intrinsic affine bridge. -/
theorem literalBase_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} Base :=
  LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT

/-- The marked Kazhdan-compression datum with its property-`(T)` premise
already discharged. -/
abbrev conceptualInclusionData :
    MarkedCompressionInclusionData Base MarkedGroup :=
  inclusionDataOfHasKazhdanPropertyT literalBase_hasKazhdanPropertyT

/-- The transported involution `d = t c t⁻¹`. -/
abbrev compressionRoot : MarkedGroup :=
  conceptualInclusionData.toKazhdanCompressionCore.transported

/-- The distinguished pointwise compression defect `u = [d,a]`. -/
abbrev compressionDefect : MarkedGroup :=
  ⁅compressionRoot, conceptualInclusionData.iota conceptualInclusionData.a⁆

/-! ## The algebraic box: `w = u²` -/

/-- The literal mark is the square of the distinguished compression defect. -/
theorem mark_eq_compressionDefect_sq : mark = compressionDefect ^ 2 := by
  have h := conceptualInclusionData.word_eq_compressionDefect_sq lamp_sq
  rw [inclusionDataOfHasKazhdanPropertyT_word] at h
  exact h

/-- The square identity together with the Clifford realization: the square
of the compression defect is genuinely nontrivial. -/
theorem compressionDefect_sq_ne_one : compressionDefect ^ 2 ≠ 1 := by
  rw [← mark_eq_compressionDefect_sq]
  exact LiteralNonMFLinearWitness.literal_mark_ne_one

/-! ## The analytic box: Kazhdan pinning -/

/-- **Kazhdan pinning.**  Every pointwise compression defect converges to the
identity in normalized Hilbert--Schmidt distance in every operator-norm
almost representation.

The finite-stage root-capture estimates are the kernel-checked realization
of the fixed-projection argument; this theorem is the conceptual interface
consumed below. -/
theorem kazhdanPinning (B : OpAlmostRepresentation MarkedGroup) :
    KazhdanCompressionCore.CompressionDefectsHSTrivial
      conceptualInclusionData.toKazhdanCompressionCore B :=
  conceptualInclusionData.toKazhdanCompressionCore.compressionDefects_hsTrivial B

/-- **The short negative-corner proof.**  A separated operator-norm almost
representation of the literal mark cuts to a nonzero corner on which the
central involution tends to `-1`.  Kazhdan transport simultaneously makes
the root defect `u` tend to `1` in normalized Hilbert--Schmidt norm and hence
makes `w = u²` tend to `1`, a contradiction.

This is the formal reader-facing endpoint; the spectral cut, polar repair,
and finite-stage transport estimates remain its checked implementation. -/
theorem negativeCorner_kazhdanTransport_contradiction
    (A : MarkedOpAlmostRepresentation MarkedGroup mark) : False := by
  rw [← inclusionDataOfHasKazhdanPropertyT_word
    literalBase_hasKazhdanPropertyT] at A
  exact KazhdanCompressorCorner.false_of_markedOpAlmostRepresentation
    conceptualInclusionData A

/-! ## The Reynolds corner -/

/-- The explicit finite normal subgroup `{1,w}` belongs to the normal
closure of the pinned compression defects. -/
theorem literalInvolutionSubgroup_le_defectNormal :
    literalInvolutionSubgroup ≤
      conceptualInclusionData.toKazhdanCompressionCore.defectNormal :=
  literalInvolutionSubgroup_le_defectNormal_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT

/-- **Reynolds-corner annihilation.**  Every map into a genuine positive-size
norm-matrix C-star corona kills the entire subgroup `{1,w}`. -/
theorem literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : MarkedGroup →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      literalInvolutionSubgroup ≤ rho.ker :=
  literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT X hX

/-- The equivalent unitary-sequence-corona kernel statement. -/
theorem literalInvolutionSubgroup_le_normMatrixCoronaKernel
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : MarkedGroup →* NormMatrixCoronaUnitary X) :
    literalInvolutionSubgroup ≤ rho.ker :=
  literalInvolutionSubgroup_le_normMatrixCoronaKernel_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT X hX rho

/-- Every norm-matrix-corona representation kills the literal Clifford
sign `w = u²`. -/
theorem literal_mark_eq_one_in_unitaryCorona
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (Theta : MarkedGroup →*
      NormMatrixCoronaUnitary (fun n ↦ naturalMatrixModel (d n))) :
    Theta mark = 1 :=
  literal_mark_eq_one_in_unitaryCorona_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT d hd Theta

/-- The mark belongs to the universal operator-norm MF residual. -/
theorem literal_mark_normMFInvisible : NormMFInvisible mark :=
  literal_mark_normMFInvisible_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT

/-! ## Clifford detection and the unconditional endpoint -/

/-- The two halves of the proof in one statement: every MF target kills the
mark, while the Clifford model proves that the mark is not the identity. -/
theorem cliffordSign_blackHole :
    NormMFInvisible mark ∧ mark ≠ 1 :=
  ⟨literal_mark_normMFInvisible,
    LiteralNonMFLinearWitness.literal_mark_ne_one⟩

/-- The literal eight-generator group is not operator-MF. -/
theorem literal_not_isOperatorMF : ¬ IsOperatorMF MarkedGroup :=
  literal_not_isOperatorMF_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT

/-- The same unconditional conclusion in the literal CDE formulation. -/
theorem literal_not_isCDEOperatorMF : ¬ IsCDEOperatorMF MarkedGroup :=
  literal_not_isCDEOperatorMF_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT

/-- The maximal group C-star algebra is not MF. -/
theorem literal_maximalGroupCStar_not_isMFAlgebra :
    ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) :=
  literal_maximalGroupCStar_not_isMFAlgebra_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT

/-- The reduced group C-star algebra is not MF. -/
theorem literal_not_isReducedGroupCStarMF :
    ¬ IsReducedGroupCStarMF MarkedGroup :=
  literal_not_isReducedGroupCStarMF_of_hasKazhdanPropertyT
    literalBase_hasKazhdanPropertyT

/-- **Unconditional manuscript Theorem A.**

The mark is a nontrivial central involution, every positive-dimensional
norm-matrix-corona representation kills it, and consequently neither the
group nor its canonical maximal and reduced group C-star algebras are MF. -/
theorem manuscriptTheoremA :
    (mark ≠ 1 ∧ mark ^ 2 = 1 ∧ ∀ g : MarkedGroup, Commute mark g) ∧
      (∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
        ∀ Theta : MarkedGroup →*
          NormMatrixCoronaUnitary (fun n ↦ naturalMatrixModel (d n)),
          Theta mark = 1) ∧
      ¬ IsOperatorMF MarkedGroup ∧
      ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) ∧
      ¬ IsReducedGroupCStarMF MarkedGroup :=
  ⟨⟨cliffordSign_blackHole.2, mark_sq, mark_central⟩,
    literal_mark_eq_one_in_unitaryCorona,
    literal_not_isOperatorMF,
    literal_maximalGroupCStar_not_isMFAlgebra,
    literal_not_isReducedGroupCStarMF⟩

/-- **Unconditional manuscript Theorem D.**

The concrete reduced group C-star algebra is separable, carries its canonical
faithful tracial state, is stably finite in the operational sense that every
isometry in every nonempty finite matrix amplification is unitary, and is not
an MF C-star algebra. -/
theorem manuscriptTheoremD :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar MarkedGroup) ∧
      Nonempty (FaithfulTracialState (ReducedGroupCStar MarkedGroup)) ∧
      (∀ (I : Type) [Fintype I] [DecidableEq I], Nonempty I →
        ∀ v : CStarMatrix I I (ReducedGroupCStar MarkedGroup),
          star v * v = 1 → v * star v = 1) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar MarkedGroup) := by
  refine ⟨reducedGroupCStar_separableSpace MarkedGroup,
    ⟨canonicalFaithfulTracialState MarkedGroup⟩, ?_,
    literal_not_isReducedGroupCStarMF⟩
  intro I _ _ hI v hv
  exact (canonicalFaithfulTracialState MarkedGroup).matrix_mul_star_eq_one_of_star_mul_eq_one
    I hI hv

end

end LiteralNonMFEndpoint
end GroupApproximation
