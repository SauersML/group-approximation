import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The finitely presented case of tex l.733-735, conditional (lane LVAssembly)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`).  Let `L = L_{𝔽₂}(1,2)` and
`C = C_2(𝔽₂)` be the Cohn algebra.  The chain:

* stable `K₂(C) = 0` (Ara–Brustenga–Cortiñas 2009, Thm 3.6);
* stable `K₂(L) = 0`, by descent along `C ↠ L` with relative `K₁` lifting;
* `Lˣ` is superperfect (Khanh arXiv:2609.08428, Thm 2.2);
* `K₂(4, L) = ⊥` (Khanh, Thm 5.1);
* the manuscript sentence (`LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFour`).

REPAIR (lane ms-sk-uncond-a).  The earlier draft of this file claimed the chain unconditionally from
`LVCohnColimit.cohn_stableK2Trivial`, which does not exist, so the module could not build.  Every
theorem now takes the one open residual,
`h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`, and delegates to the conditional
assembly `SKFix01.Assembly` (lane sk-fix-01).  LOUD: `h` is logically equivalent to stable
`K₂(C_2(𝔽₂)) = 0` (`SKFix01.skFix01_degreeZeroSurj_iff_cohn`).  Nothing here is unconditional.
-/

namespace GroupApproximation.Full.LVAssembly

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **Stable `K₂(L_{𝔽₂}(1,2)) = 0`** from the degree-zero surjectivity residual.
(Ara–Brustenga–Cortiñas 2009; `simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem binaryLeavitt_stableK2Trivial_of_degreeZeroSurj
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  SKFix01.skFix01_binaryLeavitt_stableK2Trivial h

#audit_axioms GroupApproximation.Full.LVAssembly.binaryLeavitt_stableK2Trivial_of_degreeZeroSurj

/-- **`L_{𝔽₂}(1,2)ˣ` is superperfect** (Khanh, arXiv:2609.08428, Thm 2.2), from the residual.
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
theorem binaryLeavittUnits_isSuperperfect_of_degreeZeroSurj
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVSuperperfect.IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) :=
  SKFix01.skFix01_binaryLeavittUnits_isSuperperfect h

#audit_axioms
  GroupApproximation.Full.LVAssembly.binaryLeavittUnits_isSuperperfect_of_degreeZeroSurj

/-- **`K₂(4, L_{𝔽₂}(1,2)) = ⊥`** (Khanh, arXiv:2609.08428, Thm 5.1), from the residual.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem binaryLeavittSteinbergRankFourInjective_of_degreeZeroSurj
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  SKFix01.skFix01_binaryLeavittSteinbergRankFourInjective h

#audit_axioms
  GroupApproximation.Full.LVAssembly.binaryLeavittSteinbergRankFourInjective_of_degreeZeroSurj

/-- **tex l.733-735, the finitely presented case**, from the residual.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem manuscriptSentence_finitelyPresentedCase_of_degreeZeroSurj
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
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
          (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) →
            Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
          IsMatricialVia S N φ → ∀ n : ℕ, 3 ≤ n →
            ¬ Group.IsFinitelyPresented
              ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
  SKFix01.skFix01_manuscriptSentence_finitelyPresentedCase h

#audit_axioms
  GroupApproximation.Full.LVAssembly.manuscriptSentence_finitelyPresentedCase_of_degreeZeroSurj

end GroupApproximation.Full.LVAssembly
