import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RankFourRefinement
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank four: from `K₂(4, L) = ⊥` down to finite normal generation of `K₂(4, L)`

Census row `460d289c5b0f` (tex l.733–737): "Infinite finitely presented simple Kazhdan groups
exist~\cite{CapraceRemy}, while no group in Theorem~\ref{thm:general}(b) is finitely presented: a
finitely presented LEF group is residually finite~\cite{Stepin,VershikGordon}, and an infinite simple
group is not."

Let `L = L_{𝔽₂}(1,2)`.  `LeavittFP.K2Endpoints` closes the sentence from the rank-four gap
`BinaryLeavittSteinbergRankFourInjectiveStatement`, i.e. `K₂(4, L) = ⊥`.

## Truth and route check

`K₂(4, L) = ⊥` is true: it is Khanh (arXiv:2609.08428v1), Theorem 5.4 at `r = 4`.  No elementary
Steinberg word-calculus proof was found.  The obstruction is concrete.  A contraction
`St_{n+1}(L) → St_n(L)` inverting the refinement must send `x_{r, last}(a)` to a lift of the
non-elementary matrix `1 + (s₀ a t₁) e_{rr}`, e.g. `⁅x_{rk}(s₀), x_{kr}(a t₁)⁆`.  Checking that this
respects the Steinberg relations needs the conjugation of `x_{kr}` by `x_{rk}`, which the Steinberg
relations do not determine.  That is exactly the Dennis–Stein-symbol content of `K₂`.  Stable
vanishing of `K₂(L)` goes through the localization sequence for `K_*(𝔽₂) →(1−2) K_*(𝔽₂)`, which is
also not word calculus.

## The smaller gap, and the reduction

`BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement`: `K₂(4, L)` is the normal closure
in `St_4(L)` of a finite set.

* It is implied by the old gap (`rankFourK2FinitelyNormallyGenerated_of_rankFourInjective`), because
  `⊥` is the normal closure of `∅`.
* It closes the sentence (`manuscriptSentence_finitelyPresentedCase_of_rankFourK2FinitelyNormallyGenerated`).
  `K2_map_refineHom` gives `K₂(5, L) = D(K₂(4, L))` for the surjective refinement `D`, so `K₂(5, L)`
  is finitely normally generated.  `St_5(L)` is finitely presented (`steinbergLeavitt_isFinitelyPresented`),
  so `EL_5(L) = St_5(L)/K₂(5, L)` is finitely presented.
* It is strictly weaker in logical form.  Finite normal generation of an unstable `K₂` does not force
  its vanishing: `K₂(n, ℤ) ≅ ℤ/2` for `n ≥ 3` (Milnor) is finite and nontrivial.  Nothing in the
  refinement machinery turns finitely many relators into none.  The endpoint needs only a finite
  presentation of `EL_5(L)`, not the isomorphism `St_5(L) ≅ EL_5(L)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

noncomputable section

/-- **The smaller gap.**  `K₂(4, L_{𝔽₂}(1,2))` is finitely normally generated in `St_4(L_{𝔽₂}(1,2))`.

*Why it is true.*  `K₂(4, L) = ⊥` by Khanh (arXiv:2609.08428v1), Theorem 5.4, and `⊥` is the normal
closure of the empty set (`rankFourK2FinitelyNormallyGenerated_of_rankFourInjective`).

*Why it is strictly weaker than `BinaryLeavittSteinbergRankFourInjectiveStatement`.*  The implication
from the old gap is proved here, but not the converse.  As a property of a ring and a rank, finite normal
generation of `K₂` does not imply `K₂ = ⊥`, e.g. `K₂(3, ℤ) ≅ ℤ/2`.  It asks for finitely many extra
relators presenting `EL_4(L)` over `St_4(L)`, not for none.  Not proved in Lean. -/
def BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement : Prop :=
  (BooneHigman.SteinbergBasic.K2 (Fin 4)
    (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).IsFinitelyNormallyGenerated

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement

/-- The old rank-four gap implies the smaller one. -/
theorem rankFourK2FinitelyNormallyGenerated_of_rankFourInjective
    (h : BinaryLeavittSteinbergRankFourInjectiveStatement) :
    BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement := by
  have h' : BooneHigman.SteinbergBasic.K2 (Fin 4)
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥ := h
  show (BooneHigman.SteinbergBasic.K2 (Fin 4)
    (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).IsFinitelyNormallyGenerated
  rw [h']
  exact Subgroup.IsFinitelyNormallyGenerated.bot

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.rankFourK2FinitelyNormallyGenerated_of_rankFourInjective

/-- Unconditionally, `K₂(5, L_{𝔽₂}(1,2))` is the image of `K₂(4, L_{𝔽₂}(1,2))` under the refinement
splitting the index `3` (spare index `0`). -/
theorem binaryLeavitt_K2_five_eq_map_four :
    (BooneHigman.SteinbergBasic.K2 (Fin 4) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).map
        (refineHom (GroupApproximation.BinaryLeavitt.family (ZMod 2)) (3 : Fin 4)) =
      BooneHigman.SteinbergBasic.K2 (Fin (4 + 1)) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  K2_map_refineHom (GroupApproximation.BinaryLeavitt.family (ZMod 2)) (3 : Fin 4) (0 : Fin 4)
    (by decide)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavitt_K2_five_eq_map_four

/-- `K₂(5, L_{𝔽₂}(1,2))` is finitely normally generated, from the smaller rank-four gap. -/
theorem binaryLeavittK2FiveFinitelyNormallyGenerated_of_rankFour
    (h : BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement) :
    (BooneHigman.SteinbergBasic.K2 (Fin 5)
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).IsFinitelyNormallyGenerated := by
  have h5 : (BooneHigman.SteinbergBasic.K2 (Fin (4 + 1))
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).IsFinitelyNormallyGenerated :=
    K2_isFinitelyNormallyGenerated_succ (GroupApproximation.BinaryLeavitt.family (ZMod 2))
      (3 : Fin 4) (0 : Fin 4) (by decide) h
  exact h5

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittK2FiveFinitelyNormallyGenerated_of_rankFour

/-- `EL_5(L_{𝔽₂}(1,2))` is finitely presented, from the smaller rank-four gap. -/
theorem binaryLeavittElementaryFinitelyPresented_of_rankFourK2FinitelyNormallyGenerated
    (h : BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement) :
    FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement := by
  haveI := steinbergLeavitt_isFinitelyPresented
  have h2 : Group.IsFinitelyPresented
      ↥(elementaryGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
    BooneHigman.SteinbergBasic.isFinitelyPresented_elementaryGroup_of
      (binaryLeavittK2FiveFinitelyNormallyGenerated_of_rankFour h)
  exact h2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittElementaryFinitelyPresented_of_rankFourK2FinitelyNormallyGenerated

/-- **tex l.733–737**, the whole sentence, from the smaller rank-four gap: `K₂(4, L_{𝔽₂}(1,2))` is
finitely normally generated. -/
theorem manuscriptSentence_finitelyPresentedCase_of_rankFourK2FinitelyNormallyGenerated
    (h : BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement) :
    (∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E) ∧
    (∀ (E : Type) [Group E], Group.IsFinitelyPresented E → IsLEF E → IsResiduallyFinite E) ∧
      (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E], ¬ IsResiduallyFinite E) ∧
      ∀ (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type) [TopologicalSpace Z] [CompactSpace Z]
        [TopologicalSpace.MetrizableSpace Z] [TotallyDisconnectedSpace Z] [PerfectSpace Z]
        [Nonempty Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z], MulAction.IsMinimal Λ Z →
        (∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z) →
        ∀ S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2)), 1 ∈ S →
          Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤ →
        ∀ (N : ℕ → ℕ)
          (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
          IsMatricialVia S N φ → ∀ n : ℕ, 3 ≤ n →
            ¬ Group.IsFinitelyPresented
              ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
  FPSimpleKazhdan.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented
    (binaryLeavittElementaryFinitelyPresented_of_rankFourK2FinitelyNormallyGenerated h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFourK2FinitelyNormallyGenerated

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP
