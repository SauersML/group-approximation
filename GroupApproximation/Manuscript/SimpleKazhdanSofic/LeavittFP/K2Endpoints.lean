import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementKernel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Endpoints
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(5, L_{𝔽₂}(1,2)) = ⊥` from rank four, by an elementary Leavitt refinement

Let `L = L_{𝔽₂}(1,2)`.  `LeavittFP.Endpoints` reduces the finitely presented case of tex
l.733–737 to `BinaryLeavittSteinbergInjectiveStatement`, i.e. `K₂(Fin 5, L) = ⊥`.

## Route

`LeavittFP.K2RefinementHom`, `K2RefinementDescend`, `K2RefinementSurjective`,
`K2RefinementMatrix` and `K2RefinementKernel` prove the following for every ring `R` with a
Leavitt family, `n : ℕ`, and indices `r ≠ k` in `Fin n`: if `K₂(n, R) = ⊥`, then
`K₂(n + 1, R) = ⊥` (`K2_eq_bot_succ`).

* The refinement `D : St_n(R) → St_{n+1}(R)` splits the index `r` using `t₀, t₁, s₀, s₁`.  It
  respects the three Steinberg relations, and the adjacent relation uses `s₀ t₀ + s₁ t₁ = 1`.
* `D` is onto, because a spare index `k` gives the two missing roots as commutators.
* `D` intertwines the elementary matrices along the vector refinement `refineVec`, which has
  the left inverse `contractVec`.  So `D w ∈ K₂(n + 1)` forces `w ∈ K₂(n)`.

This replaces Voronetsky's refinement isomorphism and Khanh's Lemma 5.3 on the way from rank
four to rank five.

## The remaining gap

`BinaryLeavittSteinbergRankFourInjectiveStatement`: `K₂(Fin 4, L) = ⊥`.  This is the base case
that Khanh (arXiv:2609.08428v1) proves directly through the criterion of Theorem 5.1.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

noncomputable section

/-- **The gap.**  `K₂(4, L_{𝔽₂}(1,2)) = ⊥`: the Steinberg map
`St_4(L_{𝔽₂}(1,2)) → EL_4(L_{𝔽₂}(1,2))` is injective.

*Why it is true.*  Khanh (arXiv:2609.08428v1), Theorem 5.4, states that `St_r(L) → GL_r(L)` is an
isomorphism for every `r ≥ 3` over `L = L_{𝔽₂}(1,2)`.  At `r = 4` the paper proves this directly
through its criterion, Theorem 5.1.  The other ranks come from Voronetsky's refinement.  The
image of `St_4(L)` is `E_4(L)`, so injectivity into `GL_4(L)` is exactly `K₂(4, L) = ⊥`.

*Relation to `BinaryLeavittSteinbergInjectiveStatement`.*  This statement implies rank five
(`binaryLeavittSteinbergInjective_of_rankFour`).  It is smaller in proof content: it is the
paper's base case, without the refinement step and without Lemma 5.3, and that step is proved
here elementarily.  Not proved in Lean. -/
def BinaryLeavittSteinbergRankFourInjectiveStatement : Prop :=
  BooneHigman.SteinbergBasic.K2 (Fin 4) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥

/-- `K₂(5, L_{𝔽₂}(1,2)) = ⊥` from `K₂(4, L_{𝔽₂}(1,2)) = ⊥`, by refining the index `3` of `Fin 4`
along the Leavitt family of `L_{𝔽₂}(1,2)` (spare index `0`). -/
theorem binaryLeavittSteinbergInjective_of_rankFour
    (h : BinaryLeavittSteinbergRankFourInjectiveStatement) :
    BinaryLeavittSteinbergInjectiveStatement := by
  have h5 : BooneHigman.SteinbergBasic.K2 (Fin (4 + 1))
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥ :=
    K2_eq_bot_succ (GroupApproximation.BinaryLeavitt.family (ZMod 2)) (3 : Fin 4) (0 : Fin 4)
      (by decide) h
  exact h5

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittSteinbergInjective_of_rankFour

/-- `EL_5(L_{𝔽₂}(1,2))` is finitely presented, from the rank-four gap `K₂(4, L) = ⊥`. -/
theorem binaryLeavittElementaryFinitelyPresented_of_rankFour
    (h : BinaryLeavittSteinbergRankFourInjectiveStatement) :
    FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement :=
  binaryLeavittElementaryFinitelyPresented_of_binaryLeavittSteinbergInjective
    (binaryLeavittSteinbergInjective_of_rankFour h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittElementaryFinitelyPresented_of_rankFour

/-- **tex l.733–737**, the whole sentence, from the rank-four gap `K₂(4, L_{𝔽₂}(1,2)) = ⊥`. -/
theorem manuscriptSentence_finitelyPresentedCase_of_rankFour
    (h : BinaryLeavittSteinbergRankFourInjectiveStatement) :
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
  manuscriptSentence_finitelyPresentedCase_of_binaryLeavittSteinbergInjective
    (binaryLeavittSteinbergInjective_of_rankFour h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFour

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP
