import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.CohnK2
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVWire.Chain
import GroupApproximation.Meta.AxiomGuard

/-!
# The two sentence rows of `LVWire/Chain.lean` from the degree-zero residual (lane sk-fix-01)

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-737.  The census rows
`LVWire.skLVWire_finitelyPresentedCase_of_cohnLimit` (the whole sentence) and
`LVWire.skLVWire_fpSimpleKazhdanExist_of_cohnLimit` (its first clause) instantiated at
`hD := skFix01_cohnLimit_stableK2Trivial h`, so that they depend only on
`h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement`.  Truth of `h`: see
`SKFix01/CohnK2.lean` (true; LOUD: equivalent to stable `K₂(C_2(𝔽₂)) = 0`).  Wiring only.
-/

namespace GroupApproximation.Full.SKFix01

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift in
/-- **Census row, tex l.733-737, the whole sentence**, from `h`: infinite finitely presented
simple Kazhdan groups exist; a finitely presented LEF group is residually finite; an infinite
simple group is not; and no `EL_n` (`n ≥ 3`) of a matricial clopen crossed product over `𝔽₂` is
finitely presented. -/
theorem skFix01_wire_finitelyPresentedCase
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
  LVWire.skLVWire_finitelyPresentedCase_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_finitelyPresentedCase

/-- **Census row, tex l.733-734, first clause**, from `h`: there is an infinite, finitely
presented, simple group with property (T), namely `EL_5(L_{𝔽₂}(1,2))`. -/
theorem skFix01_wire_fpSimpleKazhdanExist
    (h : LVCohnColimit.skCohnLimK2_degreeZeroSurjStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  LVWire.skLVWire_fpSimpleKazhdanExist_of_cohnLimit (skFix01_cohnLimit_stableK2Trivial h)

#audit_axioms GroupApproximation.Full.SKFix01.skFix01_wire_fpSimpleKazhdanExist

end GroupApproximation.Full.SKFix01
