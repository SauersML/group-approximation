import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.TensorModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.BrownGroupEmbedding
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GXAnswersBrownOzawaPestovClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.McDuffBrownFormulation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsBrown.BrownFormulation
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's form: `L(G) ⊗̄ 𝓡 ↪ R^ω` for `G_X` and the groups of `thm:general`

`simple_kazhdan_sofic_group.tex`:

> (tex 66–67) The groups below answer all three forms of the question positively.
>
> (l.82–84) In Brown's form, $G_X$ lies in the unitary group of the McDuff factor
> $L(G_X)\mathbin{\bar\otimes}\mathcal R$, which embeds in $\mathcal R^\omega$.
>
> (tex 350–355) Then $G$ lies in the unitary group of the McDuff factor
> $L(G)\mathbin{\bar\otimes}\mathcal R$, which embeds in
> $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq(\mathcal R\mathbin{\bar\otimes}
> \mathcal R)^\omega\cong\mathcal R^\omega$.

Route.  The closed corpus theorems (`printedSimpleKazhdanSoficMain`, `printedSimpleKazhdanGeneral`,
`FiniteModelsBrown.manuscriptSentence_lefSoficHyperlinear`) make the group infinite, finitely
generated (hence countable, `countable_of_fg`), simple and sofic.  `printedBrownFormulationFactors`
gives the McDuff factor and the injective unitary representation, and
`exists_tensorHyperfinite_embedding` gives the injective `⋆`-homomorphism `L(G) ⊗̄ 𝓡 → R^ω` for
every free ultrafilter `ω` on `ℕ`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open SymbolicDynamics.FullShift

/-- **tex 350–355**: for `G = EL_n(LC(Z, F₂) ⋊ Λ)` as in `thm:general` and a free ultrafilter `ω`
on `ℕ`, `L(G) ⊗̄ 𝓡` is a McDuff factor, `G` embeds in its unitary group, and `L(G) ⊗̄ 𝓡` embeds in
`R^ω`. -/
theorem manuscriptSentence_tensorHyperfiniteEmbedsROmega (Λ : Type) [Group Λ] [Group.FG Λ]
    (Z : Type) [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    McDuff.IsMcDuffFactor (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra
        ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))) ∧
      (∃ ψ : ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) →* unitary
          ↥(McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra
            ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))).toStarSubalgebra,
        Function.Injective ψ) ∧
      ∃ Φ : ↥(McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra
            ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))).toStarSubalgebra
          →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ := by
  obtain ⟨hinfG, hFG, hsimple, -⟩ := printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  obtain ⟨-, -, hsofic, -⟩ :=
    FiniteModelsBrown.manuscriptSentence_lefSoficHyperlinear Λ Z hmin hfree S hS1 hS N φ hφ n hn
  haveI : Countable ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
    countable_of_fg hFG
  obtain ⟨-, hMcDuff, hψ⟩ := printedBrownFormulationFactors.{0}
    ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) hsimple hinfG
  exact ⟨hMcDuff, hψ, exists_tensorHyperfinite_embedding hsofic ω hω⟩

/-- **tex l.82–84 (Brown's form of `thm:main`)**: for an infinite minimal subshift `X` over a
finite alphabet and a free ultrafilter `ω` on `ℕ`, `L(G_X) ⊗̄ 𝓡` is a McDuff factor, `G_X` embeds in
its unitary group, and `L(G_X) ⊗̄ 𝓡` embeds in `R^ω`. -/
theorem manuscriptSentence_brownFormGXEmbedsROmega (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    McDuff.IsMcDuffFactor
        (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra (G S))) ∧
      (∃ ψ : G S →* unitary
          ↥(McDuff.tensorHyperfinite
            (GroupVonNeumann.groupVonNeumannAlgebra (G S))).toStarSubalgebra,
        Function.Injective ψ) ∧
      ∃ Φ : ↥(McDuff.tensorHyperfinite
            (GroupVonNeumann.groupVonNeumannAlgebra (G S))).toStarSubalgebra
          →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ := by
  obtain ⟨hinfG, hFG, hsimple, -, -, -, hsofic, -⟩ :=
    printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  haveI : Countable (G S) := countable_of_fg hFG
  obtain ⟨-, hMcDuff, hψ⟩ := printedBrownFormulationFactors.{0} (G S) hsimple hinfG
  exact ⟨hMcDuff, hψ, exists_tensorHyperfinite_embedding hsofic ω hω⟩

/-- **tex 66–67, with the `R^ω` clause of Brown's form**: some infinite minimal subshift
`X ⊆ Bool^ℤ` makes `G_X` an infinite simple sofic hyperlinear group with property (T), with `L(G_X)`
a II₁ factor, `L(G_X) ⊗̄ 𝓡` a McDuff factor containing `G_X` in its unitary group, and
`L(G_X) ⊗̄ 𝓡` embedding in `R^ω` for every free ultrafilter `ω` on `ℕ`. -/
theorem manuscriptSentence_groupsAnswerAllThreeForms :
    ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧ Infinite (G S) ∧
      IsSimpleGroup (G S) ∧ HasKazhdanPropertyT.{0, 0} (G S) ∧ IsSofic (G S) ∧
      IsHyperlinear (G S) ∧
      IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra (G S)) ∧
      McDuff.IsMcDuffFactor
        (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra (G S))) ∧
      (∃ ψ : G S →* unitary
          ↥(McDuff.tensorHyperfinite
            (GroupVonNeumann.groupVonNeumannAlgebra (G S))).toStarSubalgebra,
        Function.Injective ψ) ∧
      ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
        ∃ Φ : ↥(McDuff.tensorHyperfinite
            (GroupVonNeumann.groupVonNeumannAlgebra (G S))).toStarSubalgebra
          →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ := by
  obtain ⟨S, hSinf, hmin, hinf, hsimple, hT, hsofic, hhyp⟩ := printedGXAnswersBrownOzawaPestov
  obtain ⟨-, hFG, -⟩ := printedSimpleKazhdanSoficMain Bool S hSinf hmin 3 le_rfl
  haveI : Countable (G S) := countable_of_fg hFG
  obtain ⟨hII, hMcDuff, hψ⟩ := printedBrownFormulationFactors.{0} (G S) hsimple hinf
  exact ⟨S, hSinf, hmin, hinf, hsimple, hT, hsofic, hhyp, hII, hMcDuff, hψ,
    fun ω hω ↦ exists_tensorHyperfinite_embedding hsofic ω hω⟩

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.manuscriptSentence_tensorHyperfiniteEmbedsROmega
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.manuscriptSentence_brownFormGXEmbedsROmega
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.manuscriptSentence_groupsAnswerAllThreeForms
