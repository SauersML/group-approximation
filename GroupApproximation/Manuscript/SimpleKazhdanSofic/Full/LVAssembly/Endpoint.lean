-- DRAFT (not landed, not compiled). Lane LVAssembly, unconditional endpoint for tex l.733-735.
-- Land as Full/LVAssembly/Endpoint.lean once `LVCohnColimit.cohn_stableK2Trivial` is on
-- origin/main (expected module Full/LVCohnColimit/Final.lean, draft
-- fk/drafts/LVCohnColimit-Final.lean).  Nothing else is missing: S2/S3 enter only upstream
-- (inside cohn_stableK2Trivial), not here.
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Final
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Lift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.RelSix
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.KTwoFour
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.RankThree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints

/-!
# The finitely presented case of tex l.733-735, unconditionally (lane LVAssembly)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`).  Let `L = L_{𝔽₂}(1,2)` and
`C = C_2(𝔽₂)` the Cohn algebra.  The chain is:

* stable `K₂(C) = 0` (`LVCohnColimit.cohn_stableK2Trivial`; Ara–Brustenga–Cortiñas 2009,
  Thm 3.6);
* stable `K₂(L) = 0`, by descent along the surjection `C ↠ L` with relative `K₁` lifting
  (`LVStableK2.stableK2Trivial_of_surjective`, `LVCohnRelK1.cohn_relativeKOneLift`);
* `Lˣ` is superperfect (`LVStability.binaryLeavittUnits_isSuperperfect_of_stableK2Trivial`;
  Khanh arXiv:2609.08428, Thm 2.2);
* `K₂(3, L) ≤ ⁅St_3(L), K₂(3, L)⁆` (`LeavittK2.K2_three_le_commutator_of_superperfect`);
* `K₂(4, L) = ⊥` (`k2Four_eq_bot_of_le_commutator`; Khanh, Thm 5.1);
* the manuscript sentence (`LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFour`).
-/

namespace GroupApproximation.Full.LVAssembly

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **Stable `K₂(L_{𝔽₂}(1,2)) = 0`** (route W1): stable `K₂(C_2(𝔽₂)) = 0` descends along the
Cohn surjection `C_2(𝔽₂) ↠ L_{𝔽₂}(1,2)`, which has relative `K₁` lifting.
(Ara–Brustenga–Cortiñas 2009; `simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem binaryLeavitt_stableK2Trivial : LVH2GL3.StableK2Trivial BinL :=
  LVStableK2.stableK2Trivial_of_surjective LVCohnRelK1.toLeavitt LVCohnRelK1.toLeavitt_surjective
    LVCohnRelK1.cohn_relativeKOneLift LVCohnColimit.cohn_stableK2Trivial

/-- **`L_{𝔽₂}(1,2)ˣ` is superperfect** (Khanh, arXiv:2609.08428, Thm 2.2), from stable
`K₂(L) = 0`.  (`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
theorem binaryLeavittUnits_isSuperperfect : LVSuperperfect.IsSuperperfect (BinLˣ) :=
  LVStability.binaryLeavittUnits_isSuperperfect_of_stableK2Trivial binaryLeavitt_stableK2Trivial

/-- **`K₂(4, L_{𝔽₂}(1,2)) = ⊥`** (Khanh, arXiv:2609.08428, Thm 5.1), unconditionally.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem binaryLeavittSteinbergRankFourInjective :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  k2Four_eq_bot_of_le_commutator
    (Manuscript.SimpleKazhdanSofic.LeavittK2.K2_three_le_commutator_of_superperfect
      binaryLeavittUnits_isSuperperfect)

/-- **tex l.733-735, the finitely presented case, unconditionally.**  There is an infinite
finitely presented simple group with property (T); finitely presented LEF groups are residually
finite; infinite simple groups are not; and for every minimal topologically free Cantor action
of a finitely generated group whose clopen crossed product over `𝔽₂` is matricial, no
`EL_n` (`n ≥ 3`) of that crossed product is finitely presented.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem manuscriptSentence_finitelyPresentedCase :
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
  Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFour
    binaryLeavittSteinbergRankFourInjective

end GroupApproximation.Full.LVAssembly
