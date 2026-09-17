import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Manuscript.SimpleKazhdanSofic.McDuffBrownFormulation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.InfiniteSimpleICC
import GroupApproximation.Analysis.McDuffTensorHyperfinite
import GroupApproximation.Analysis.McDuffFactor
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# "Brown's formulation", tex 345–355

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":

> (tex 345) Let $G$ be a group as in Theorem~\ref{thm:general}\textup{(b)}.
> (tex 345–348) It is LEF, so it is sofic [Pestov, Example 4.5] and hyperlinear [ElekSzabo,
> Theorem 2], and $L(G)$ embeds in $\mathcal R^\omega$ [Kirchberg, Radulescu], [Ozawa, Prop. 7.1].
> (tex 349–350) As $G$ is infinite and simple, its nontrivial conjugacy classes are infinite, so
> $L(G)$ is a $\mathrm{II}_1$ factor.
> (tex 350–355) Then $G$ lies in the unitary group of the McDuff factor
> $L(G)\mathbin{\bar\otimes}\mathcal R$ [McDuff], which embeds in
> $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq(\mathcal R\mathbin{\bar\otimes}\mathcal R)^\omega
> \cong\mathcal R^\omega$, as in Brown's question.

Every endpoint carries the full hypotheses of `thm:general` and is stated for every rank `n ≥ 3`, with
`G = EL_n(LC(Z, F₂) ⋊ Λ)`.

Proof route:

* LEF: the marked limit of `printedSimpleKazhdanGeneral` and `isTextbookLEF_of_isMarkedLimit`,
  `isLEF_of_isMarkedLimit`; sofic: `isSofic_of_isLEF` (proved, the special case of Pestov's example);
  hyperlinear: `isHyperlinear_of_isSofic` (proved, Elek–Szabó). The embedding `L(G) ↪ R^ω` is not
  available in the corpus (see the row file).
* ICC and II₁ factor: `isICC_of_isSimpleGroup_of_infinite`,
  `IIOneFactor.isIIOneFactor_groupVonNeumannAlgebra`.
* McDuff and the unitary group: `printedBrownFormulationFactors` (`McDuff.isMcDuffFactor_tensorHyperfinite`,
  `McDuff.groupUnitaryHom_injective`). The embedding `L(G) ⊗̄ R ↪ R^ω` is not available in the corpus.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace FiniteModelsBrown

/-- **tex 345–348**, the group-theoretic part: for `G = EL_n(LC(Z, F₂) ⋊ Λ)` as in `thm:general`,
`G` is LEF (textbook and corpus forms), hence sofic, hence hyperlinear. -/
theorem manuscriptSentence_lefSoficHyperlinear (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) :
    IsTextbookLEF ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      IsLEF ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      IsSofic ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      IsHyperlinear ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) := by
  obtain ⟨-, -, -, -, hlim, -, -, -⟩ :=
    printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  have hfin : ∀ k, Finite ↥(elementaryGroup (Fin n) (Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))) :=
    fun k => finite_elementaryGroup_matrix n (N k)
  have hLEF := isLEF_of_isMarkedLimit hfin hlim
  have hsofic := isSofic_of_isLEF hLEF
  exact ⟨isTextbookLEF_of_isMarkedLimit hfin hlim, hLEF, hsofic, isHyperlinear_of_isSofic hsofic⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_lefSoficHyperlinear

/-- **tex 349–350**: for `G` as in `thm:general`, `G` is infinite and simple, its nontrivial
conjugacy classes are infinite, and `L(G)` is a II₁ factor. -/
theorem manuscriptSentence_iccIIOneFactor (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) :
    Infinite ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      IsSimpleGroup ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      TwoSidedRegularCommutant.IsICC
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) ∧
      IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))) := by
  obtain ⟨hInf, -, hG, -⟩ := printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  haveI := hInf
  haveI := hG
  have hICC := isICC_of_isSimpleGroup_of_infinite
    ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
  exact ⟨hInf, hG, hICC, IIOneFactor.isIIOneFactor_groupVonNeumannAlgebra
    ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) hICC⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_iccIIOneFactor

/-- **tex 350–355**, all clauses but the embedding into `R^ω`: for `G` as in `thm:general`,
`L(G) ⊗̄ R` is a McDuff factor, and `G` lies in its unitary group (`g ↦ λ(g) ⊗ 1` is an injective
homomorphism into the unitary group). -/
theorem manuscriptSentence_mcDuffUnitaryEmbedding (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) :
    McDuff.IsMcDuffFactor (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))) ∧
      ∃ ψ : ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) →* unitary
          ↥(McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra
            ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))).toStarSubalgebra,
        Function.Injective ψ := by
  obtain ⟨hInf, -, hG, -⟩ := printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  obtain ⟨-, hMcDuff, hψ⟩ := printedBrownFormulationFactors.{0}
    ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) hG hInf
  exact ⟨hMcDuff, hψ⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.FiniteModelsBrown.manuscriptSentence_mcDuffUnitaryEmbedding

end FiniteModelsBrown
end SimpleKazhdanSofic
end GroupApproximation
