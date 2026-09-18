import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.Wire
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.WireSentence
import GroupApproximation.Meta.AxiomGuard

/-!
# Census: every SK consequence of the degree-zero residual (lane sk-fix-01)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-737.  One theorem,
`skFix01_census`, listing, from the single hypothesis
`h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement` (stable surjectivity of
`K₂(C₀) → K₂(C_2(𝔽₂))`), every downstream statement of the stable-`K₂` chain.  Write
`C = C_2(𝔽₂)`, `L = L_{𝔽₂}(1,2)`, `D = CohnLimit`.  The conjuncts, in order:

1. stable `K₂(D) = 0` (the `LVWire` hypothesis `hD`);
2. stable `K₂(C) = 0` (`LVWire` row #2; ABC 2009, Thm 3.6);
3. `K₂(𝔽₂) → K₂(C)` stably surjective (the draft `LVCohnK2.cohn_stableK2BaseSurjective`);
4. stable `K₂(LeavittK2.CohnTwo (ZMod 2)) = 0` and 5. its registered form;
6. stable `K₂(L) = 0` (row #3) and 7. its registered form;
8. `Lˣ` superperfect (`LVSuperperfect.IsSuperperfect`) and 9. the binder `hsp` (row #4);
10. `K₂(4, L) = ⊥` (row #5), 11. `K₂(5, L) = ⊥` (row #6), 12. `EL_5(L)` finitely presented
    (row #7);
13. the padding `St_3(L) → St_4(L)` kills `K₂(3, L)` (row #8), 14. the interface `#8 → #5`
    (row #9);
15. the first clause of tex l.733-734 (infinite finitely presented simple Kazhdan groups exist);
16. the whole sentence tex l.733-737 (finitely presented case).

LOUD: `h` is logically equivalent to conjunct 2 (`skFix01_degreeZeroSurj_iff_cohn`), and is true
by ABC 2009, Thm 3.6.  Nothing here is unconditional.
-/

namespace GroupApproximation.Full.SKFix01

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift in
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP in
open GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan in
/-- **Census of the SK consequences of `h`** (sixteen conjuncts, listed in the module
docstring).  (`simple_kazhdan_sofic_group.tex` l.733-737, `sec:questions`.) -/
theorem skFix01_census (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial LVCohnColimit.CohnLimit ∧
    LVH2GL3.StableK2Trivial LVCohnRelK1.CohnTwoF2 ∧
    LVStableK2.StableK2BaseSurjective LVCohnRelK1.cohnUnit ∧
    LVH2GL3.StableK2Trivial (CohnTwo (ZMod 2)) ∧
    BinaryCohnStableK2TrivialStatement ∧
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ∧
    BinaryLeavittStableK2TrivialStatement ∧
    LVSuperperfect.IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) ∧
    EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement ∧
    BinaryLeavittSteinbergRankFourInjectiveStatement ∧
    BinaryLeavittSteinbergInjectiveStatement ∧
    BinaryLeavittElementaryFinitelyPresentedStatement ∧
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement ∧
    EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement ∧
    (∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E) ∧
    ((∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
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
              ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))) :=
  ⟨skFix01_cohnLimit_stableK2Trivial h, skFix01_wire_cohnStableK2 h,
    skFix01_cohn_stableK2BaseSurjective h, skFix01_wire_cohnTwoStableK2 h,
    skFix01_wire_binaryCohnStatement h, skFix01_wire_leavittStableK2 h,
    skFix01_wire_binaryLeavittStatement h, skFix01_binaryLeavittUnits_isSuperperfect h,
    skFix01_wire_unitsSuperperfect h, skFix01_wire_rankFourInjective h,
    skFix01_wire_steinbergInjective h, skFix01_wire_elementaryFP h,
    skFix01_wire_stabKernelThreeTrivial h, skFix01_wire_rankFourOfStabKernelThree h,
    skFix01_wire_fpSimpleKazhdanExist h, skFix01_wire_finitelyPresentedCase h⟩

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_census

end GroupApproximation.Full.SKFix01
