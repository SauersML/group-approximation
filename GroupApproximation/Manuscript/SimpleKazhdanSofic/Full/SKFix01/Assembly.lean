import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.CohnK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnRelK1.Lift
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSuperperfect.Superperfect
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVStability.RelSix
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVAssembly.KTwoFour
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.RankThree
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Conditional form of the stale draft `LVAssembly/Endpoint.lean` (lane sk-fix-01)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`).  The draft
`Full/LVAssembly/Endpoint.lean` cites the removed `LVCohnColimit.cohn_stableK2Trivial`.  This
module proves its four theorems from the single hypothesis
`h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement` (stable surjectivity of
`K₂(C₀) → K₂(C)`), along the draft's own chain, with `L = L_{𝔽₂}(1,2)`, `C = C_2(𝔽₂)`:

* stable `K₂(C) = 0` (`SKFix01.skFix01_cohn_stableK2Trivial`);
* stable `K₂(L) = 0`, by descent along `C ↠ L` with relative `K₁` lifting;
* `Lˣ` is superperfect (Khanh arXiv:2609.08428, Thm 2.2);
* `K₂(3, L) ≤ ⁅St_3(L), K₂(3, L)⁆`, hence `K₂(4, L) = ⊥` (Khanh, Thm 5.1);
* the manuscript sentence (`LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFour`).

Only difference from the draft: the superperfect binder is converted to
`EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement` explicitly by
`LVSuperperfect.isSuperperfect_binaryLeavittUnits_iff.mp` (as in `LVWire/Chain.lean`), rather
than by definitional unfolding.  Truth of `h`: see `SKFix01/CohnK2.lean` (true; LOUD: equivalent
to stable `K₂(C) = 0`).
-/

namespace GroupApproximation.Full.SKFix01

/-- **Stable `K₂(L_{𝔽₂}(1,2)) = 0`** from `h`: stable `K₂(C_2(𝔽₂)) = 0` descends along the Cohn
surjection `C_2(𝔽₂) ↠ L_{𝔽₂}(1,2)`, which has relative `K₁` lifting.  Conditional replacement
of the draft `LVAssembly.binaryLeavitt_stableK2Trivial`.  (Ara–Brustenga–Cortiñas 2009;
`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skFix01_binaryLeavitt_stableK2Trivial
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  LVStableK2.stableK2Trivial_of_surjective LVCohnRelK1.toLeavitt LVCohnRelK1.toLeavitt_surjective
    LVCohnRelK1.cohn_relativeKOneLift (skFix01_cohn_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_binaryLeavitt_stableK2Trivial

/-- **`L_{𝔽₂}(1,2)ˣ` is superperfect** (Khanh, arXiv:2609.08428, Thm 2.2), from `h`.
Conditional replacement of the draft `LVAssembly.binaryLeavittUnits_isSuperperfect`.
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
theorem skFix01_binaryLeavittUnits_isSuperperfect
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    LVSuperperfect.IsSuperperfect ((BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ) :=
  LVStability.binaryLeavittUnits_isSuperperfect_of_stableK2Trivial
    (skFix01_binaryLeavitt_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_binaryLeavittUnits_isSuperperfect

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 in
/-- **The superperfect binder `hsp` in its registered form**, from `h`.
(`simple_kazhdan_sofic_group.tex` l.733-735, binder `hsp`.) -/
theorem skFix01_unitsSuperperfectStatement
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  LVSuperperfect.isSuperperfect_binaryLeavittUnits_iff.mp
    (skFix01_binaryLeavittUnits_isSuperperfect h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_unitsSuperperfectStatement

/-- **`K₂(4, L_{𝔽₂}(1,2)) = ⊥`** (Khanh, arXiv:2609.08428, Thm 5.1), from `h`.  Conditional
replacement of the draft `LVAssembly.binaryLeavittSteinbergRankFourInjective`.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skFix01_binaryLeavittSteinbergRankFourInjective
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  LVAssembly.k2Four_eq_bot_of_le_commutator
    (Manuscript.SimpleKazhdanSofic.LeavittK2.K2_three_le_commutator_of_superperfect
      (skFix01_unitsSuperperfectStatement h))

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_binaryLeavittSteinbergRankFourInjective

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift in
/-- **tex l.733-735, the finitely presented case, from `h`.**  There is an infinite finitely
presented simple group with property (T); finitely presented LEF groups are residually finite;
infinite simple groups are not; and for every minimal topologically free Cantor action of a
finitely generated group whose clopen crossed product over `𝔽₂` is matricial, no `EL_n`
(`n ≥ 3`) of that crossed product is finitely presented.  Conditional replacement of the draft
`LVAssembly.manuscriptSentence_finitelyPresentedCase`.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skFix01_manuscriptSentence_finitelyPresentedCase
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
  Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFour
    (skFix01_binaryLeavittSteinbergRankFourInjective h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_manuscriptSentence_finitelyPresentedCase

end GroupApproximation.Full.SKFix01
