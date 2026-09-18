import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.EmbeddingLimit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStableK2.Reduction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Cohn
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Lift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSuperperfect.Superperfect
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.RelSix
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.KTwoFour
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCentral.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.RankThree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.Padded
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.CapraceRemyGap
import GroupApproximation.Meta.AxiomGuard

/-!
# The finitely presented case of tex l.733-735 from stable `K₂` of the Cohn colimit

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735.  Let `C = C_2(𝔽₂)` be the Cohn
algebra, `L = L_{𝔽₂}(1,2)`, and `D = CohnLimit` the colimit of `C × 𝔽₂` along the corner maps
`θ_M` (`LVCohnColimit.EmbeddingLimit`).  This module has ONE hypothesis,
`hD : LVH2GL3.StableK2Trivial CohnLimit`, and derives, in order:

* #2 stable `K₂(C) = 0` (`LVCohnColimit.stableK2Trivial_of_cohnColimit`; ABC 2009, Thm 3.6);
* #3 stable `K₂(L) = 0`, by descent along `C ↠ L` with relative `K₁` lifting
  (`LVStableK2.stableK2Trivial_of_surjective`, `LVCohnRelK1.cohn_relativeKOneLift`);
* #4 `Lˣ` is superperfect (`LVStability.binaryLeavittUnits_isSuperperfect_of_stableK2Trivial`;
  Khanh arXiv:2609.08428, Thm 2.2);
* #5 `K₂(4, L) = ⊥` (`LeavittK2.K2_three_le_commutator_of_superperfect`,
  `LVAssembly.k2Four_eq_bot_of_le_commutator`; Khanh, Thm 5.1);
* #6 `K₂(5, L) = ⊥` and #7 `EL_5(L)` finitely presented (`LeavittFP`);
* #8 the padding `St_3(L) → St_4(L)` kills `K₂(3, L)` (`LeavittK2.Padded`, `LVCentral`);
* #9 the implication `#8 → #5` (trivially, since `#5` holds);
* the census rows of `FPSimpleKazhdan.CapraceRemyGap`: the whole sentence and its first clause.

Truth: `hD` is true (Ara–Brustenga–Cortiñas: `K₂` commutes with filtered colimits,
`K₂(C × 𝔽₂) = K₂(C) ⊕ K₂(𝔽₂) = K₂(C)`, `θ_M` acts trivially on `K₂(C)`, and `K₂(C) = K₂(𝔽₂) = 0`).
It is essentially EQUIVALENT to #2, not strictly smaller: this module is wiring only.
-/

namespace GroupApproximation.Full.LVWire

/-- **#2: stable `K₂(C_2(𝔽₂)) = 0`** from stable `K₂` of the Cohn colimit (ABC 2009, Thm 3.6;
tex l.733-735). -/
theorem skLVWire_cohnStableK2_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 := by
  rcases LVCohnColimit.exists_cohnColimit_embedding_of_stableK2Trivial hD with
    ⟨D, instD, hD', ι, hinj, hunion, hcompat⟩
  exact @LVCohnColimit.stableK2Trivial_of_cohnColimit D instD hD' ι hinj hunion hcompat

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_cohnStableK2_of_cohnLimit

/-- **#3: stable `K₂(L_{𝔽₂}(1,2)) = 0`**, by descent along `C_2(𝔽₂) ↠ L_{𝔽₂}(1,2)`
(tex l.733-735). -/
theorem skLVWire_leavittStableK2_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  LVStableK2.stableK2Trivial_of_surjective LVCohnRelK1.toLeavitt LVCohnRelK1.toLeavitt_surjective
    LVCohnRelK1.cohn_relativeKOneLift (skLVWire_cohnStableK2_of_cohnLimit hD)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_leavittStableK2_of_cohnLimit

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **#4: `L_{𝔽₂}(1,2)ˣ` is superperfect** (Khanh, Thm 2.2; tex l.733-735, binder `hsp`). -/
theorem skLVWire_unitsSuperperfect_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  LVSuperperfect.isSuperperfect_binaryLeavittUnits_iff.mp
    (LVStability.binaryLeavittUnits_isSuperperfect_of_stableK2Trivial
      (skLVWire_leavittStableK2_of_cohnLimit hD))

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_unitsSuperperfect_of_cohnLimit

/-- **#5: `K₂(4, L_{𝔽₂}(1,2)) = ⊥`** (Khanh, Thm 5.1; tex l.733-735). -/
theorem skLVWire_rankFourInjective_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  LVAssembly.k2Four_eq_bot_of_le_commutator
    (Manuscript.SimpleKazhdanSofic.LeavittK2.K2_three_le_commutator_of_superperfect
      (skLVWire_unitsSuperperfect_of_cohnLimit hD))

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_rankFourInjective_of_cohnLimit

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP in
/-- **#6: `K₂(5, L_{𝔽₂}(1,2)) = ⊥`** (Khanh, Thm 5.4; tex l.733-735). -/
theorem skLVWire_steinbergInjective_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    BinaryLeavittSteinbergInjectiveStatement :=
  binaryLeavittSteinbergInjective_of_rankFour (skLVWire_rankFourInjective_of_cohnLimit hD)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_steinbergInjective_of_cohnLimit

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP in
open GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan in
/-- **#7: `EL_5(L_{𝔽₂}(1,2))` is finitely presented** (Khanh, Thm 5.4 and Lemma 5.3;
tex l.733-735). -/
theorem skLVWire_elementaryFP_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    BinaryLeavittElementaryFinitelyPresentedStatement :=
  binaryLeavittElementaryFinitelyPresented_of_binaryLeavittSteinbergInjective
    (skLVWire_steinbergInjective_of_cohnLimit hD)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_elementaryFP_of_cohnLimit

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **#8: the padding `St_3(L) → St_4(L)` kills `K₂(3, L)`**, from the closed padded-central
statement and #4 (Khanh, Thm 2.2; tex l.733-735). -/
theorem skLVWire_stabKernelThreeTrivial_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement :=
  stabKernelThreeTrivial_of_paddedCentral_of_superperfect
    LVCentral.binaryLeavittPaddedCentralThree (skLVWire_unitsSuperperfect_of_cohnLimit hD)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_stabKernelThreeTrivial_of_cohnLimit

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **#9: the interface `#8 → #5`**, which holds because its conclusion #5 holds
(tex l.733-735). -/
theorem skLVWire_rankFourOfStabKernelThree_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement :=
  fun _ => skLVWire_rankFourInjective_of_cohnLimit hD

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_rankFourOfStabKernelThree_of_cohnLimit

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift in
open GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan in
/-- **Census row, tex l.733-737, the whole sentence**, from `hD` alone: infinite finitely
presented simple Kazhdan groups exist; a finitely presented LEF group is residually finite; an
infinite simple group is not; and no `EL_n` (`n ≥ 3`) of a matricial clopen crossed product over
`𝔽₂` is finitely presented.  Instance at #7 of the `FPSimpleKazhdan` theorem
`manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented`. -/
theorem skLVWire_finitelyPresentedCase_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
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
  manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented
    (skLVWire_elementaryFP_of_cohnLimit hD)

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_finitelyPresentedCase_of_cohnLimit

/-- **Census row, tex l.733-734, first clause**, from `hD` alone: there is an infinite, finitely
presented, simple group with property (T), namely `EL_5(L_{𝔽₂}(1,2))`.  This is the conclusion of
`FPSimpleKazhdan.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_...`
(whose 112-character name cannot fit a line), taken as the first conjunct of the whole
sentence. -/
theorem skLVWire_fpSimpleKazhdanExist_of_cohnLimit
    (hD : LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  (skLVWire_finitelyPresentedCase_of_cohnLimit hD).1

#audit_axioms GroupApproximation.Full.LVWire.skLVWire_fpSimpleKazhdanExist_of_cohnLimit

end GroupApproximation.Full.LVWire
