import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKFix01.Assembly
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVK2Route.Core
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFreeAlgK2.ZModTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# The SK open row from Gersten and the `K₂` localization step (lane ms-sk-uncond-a)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  This module states
the two open inputs precisely and wires them straight to the manuscript sentence.  The route
skips the Cohn colimit: `L = L_{𝔽₂}(1,2)` is the universal localization of the free algebra
`F = 𝔽₂⟨x₀,x₁⟩` (Cohn), along `LVK2Route.freeToLeavitt : F → L`, `xᵢ ↦ sᵢ`.

* `skLoc_GerstenTwoStatement`: the Gersten nil part of `K₂(F)` vanishes, i.e.
  `LVFreeAlgK2.AugNilK2Trivial (freeAug (ZMod 2) (Fin 2))`.  Gersten, *K-theory of free rings*,
  Comm. Algebra 1 (1974).  Only the one-generator case is proved in Lean
  (`LVPolyK2.skPolyK2_augNil_freeAlgebra_one_zmodTwo`).  That proof does NOT generalize: it
  uses `𝔽₂⟨x⟩ ≅ 𝔽₂[x]` and the Euclidean (Nagao-type) proof of `K₂(N, 𝔽_p[X]) = ⊥`.  For two
  generators the ring is noncommutative and not Euclidean; the analogue would have to run on
  Cohn's weak algorithm.
* `skLoc_LocalizationStatement`: the degree-two localization step, stable surjectivity of
  `K₂(F) → K₂(L)` (`LVStableK2.StableK2BaseSurjective freeToLeavitt`, Core-B of `LVK2Route`).
  Source: the localization sequence `K₂(F) → K₂(L) → K₁(T) → K₁(F)` for the stably flat
  universal localization `F → L` (Neeman–Ranicki, *Noncommutative localisation in algebraic
  K-theory I*, Geom. Topol. 8 (2004); stable flatness since `F` is a fir, Bergman–Dicks 1978),
  where `K₁(T) → K₁(F)` is injective.
* `skLoc_leavittStableK2_of_gersten_of_localization`: together they give stable `K₂(L) = 0`.
* `skLoc_manuscriptSentence_of_leavittStableK2` and
  `skLoc_manuscriptSentence_of_gersten_of_localization`: the sentence of tex l.733-735.

**Published value (checked at source).**  Stable `K₂(L_{𝔽₂}(1,2)) = 0` is published.
Ara–Brustenga–Cortiñas, *K-theory of Leavitt path algebras*, Münster J. Math. 2 (2009),
arXiv:0903.0056v2, Theorem 7.6: for a regular supercoherent `k` (every field is one) and a
row-finite quiver `E`, there is a long exact sequence
`K_n(k)^(E⁰∖Sink E) --(1 - N_Eᵗ)--> K_n(k)^(E⁰) → K_n(L_k(E)) → K_(n-1)(k)^(E⁰∖Sink E)`.
For `L(1,2)`, `E` is one vertex with two loops, `N_E = (2)` and `1 - N_Eᵗ = -1`, so every
`K_n(L_{𝔽₂}(1,2))` vanishes.  (Text read on MSI, `lit-groups/abc-clean.txt` l.1064-1075.)  In
Lean this is still OWED: `skLoc_manuscriptSentence_of_leavittStableK2` takes it as its one
hypothesis.  LOUD: given Gersten, `skLoc_LocalizationStatement` is equivalent to it
(`LVK2Route.freeBaseSurjective_iff_stableK2Trivial`), so the pair is not weaker than the target.
-/

namespace GroupApproximation.Full.LVPolyK2

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- **Gersten for two generators**: the augmentation nil part of stable `K₂(𝔽₂⟨x₀,x₁⟩)`
vanishes (Gersten 1974).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skLoc_GerstenTwoStatement : Prop :=
  LVFreeAlgK2.AugNilK2Trivial (LVFreeAlgK2.freeAug (ZMod 2) (Fin 2))

/-- **The `K₂` localization step**: `K₂(𝔽₂⟨x₀,x₁⟩) → K₂(L_{𝔽₂}(1,2))` is stably onto
(Neeman–Ranicki 2004; Bergman–Dicks 1978).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def skLoc_LocalizationStatement : Prop :=
  LVStableK2.StableK2BaseSurjective LVK2Route.freeToLeavitt

/-- Gersten for two generators gives stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0` (with `K₂(𝔽₂) = 0`).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skLoc_freeStableK2_of_gersten (hG : skLoc_GerstenTwoStatement) :
    LVH2GL3.StableK2Trivial (FreeAlgebra (ZMod 2) (Fin 2)) :=
  (LVFreeAlgK2.stableK2Trivial_freeAlgebra_zmodTwo_iff (Fin 2)).mpr hG

#audit_axioms GroupApproximation.Full.LVPolyK2.skLoc_freeStableK2_of_gersten

/-- **Stable `K₂(L_{𝔽₂}(1,2)) = 0`** from Gersten and the localization step.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skLoc_leavittStableK2_of_gersten_of_localization (hG : skLoc_GerstenTwoStatement)
    (hL : skLoc_LocalizationStatement) :
    LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
  LVK2Route.binaryLeavitt_stableK2Trivial_of_freeBaseSurjective hL
    (skLoc_freeStableK2_of_gersten hG)

#audit_axioms GroupApproximation.Full.LVPolyK2.skLoc_leavittStableK2_of_gersten_of_localization

/-- LOUD: the localization step follows from stable `K₂(L) = 0` (ABC 2009, Thm 7.6).
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skLoc_localization_of_leavittStableK2
    (h : LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    skLoc_LocalizationStatement :=
  LVK2Route.freeBaseSurjective_of_stableK2Trivial h

#audit_axioms GroupApproximation.Full.LVPolyK2.skLoc_localization_of_leavittStableK2

/-- **`K₂(4, L_{𝔽₂}(1,2)) = ⊥`** from stable `K₂(L) = 0`: superperfect units (Khanh,
arXiv:2609.08428, Thm 2.2), then Khanh, Thm 5.1.  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skLoc_rankFourInjective_of_leavittStableK2
    (h : LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    Manuscript.SimpleKazhdanSofic.LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  LVAssembly.k2Four_eq_bot_of_le_commutator
    (Manuscript.SimpleKazhdanSofic.LeavittK2.K2_three_le_commutator_of_superperfect
      (LVSuperperfect.isSuperperfect_binaryLeavittUnits_iff.mp
        (LVStability.binaryLeavittUnits_isSuperperfect_of_stableK2Trivial h)))

#audit_axioms GroupApproximation.Full.LVPolyK2.skLoc_rankFourInjective_of_leavittStableK2

/-- **tex l.733-735, the finitely presented case**, from stable `K₂(L_{𝔽₂}(1,2)) = 0`
(published: ABC 2009, Thm 7.6; owed in Lean).  (`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skLoc_manuscriptSentence_of_leavittStableK2
    (h : LVH2GL3.StableK2Trivial (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
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
    (skLoc_rankFourInjective_of_leavittStableK2 h)

#audit_axioms GroupApproximation.Full.LVPolyK2.skLoc_manuscriptSentence_of_leavittStableK2

/-- **tex l.733-735, first clause**, from Gersten and the localization step.
(`simple_kazhdan_sofic_group.tex` l.733-735.) -/
theorem skLoc_manuscriptSentence_of_gersten_of_localization (hG : skLoc_GerstenTwoStatement)
    (hL : skLoc_LocalizationStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  (skLoc_manuscriptSentence_of_leavittStableK2
    (skLoc_leavittStableK2_of_gersten_of_localization hG hL)).1

#audit_axioms
  GroupApproximation.Full.LVPolyK2.skLoc_manuscriptSentence_of_gersten_of_localization

end GroupApproximation.Full.LVPolyK2
