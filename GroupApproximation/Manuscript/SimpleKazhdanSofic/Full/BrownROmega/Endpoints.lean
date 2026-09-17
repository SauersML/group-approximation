import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.Factors
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.GroupModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.BrownROmega.TensorModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.MainTheorem.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.GeneralExpanders.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.WordProblems.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown's formulation: endpoints (M2, T3, "Brown's formulation")

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation" (tex l.344–355):

> Let $G$ be a group as in Theorem~\ref{thm:general}\textup{(b)}. It is LEF, so it is sofic and
> hyperlinear, and $L(G)$ embeds in $\mathcal R^\omega$. As $G$ is infinite and simple, its
> nontrivial conjugacy classes are infinite, so $L(G)$ is a $\mathrm{II}_1$ factor. Then $G$ lies
> in the unitary group of the McDuff factor $L(G)\mathbin{\bar\otimes}\mathcal R$, which embeds in
> $\mathcal R^\omega\mathbin{\bar\otimes}\mathcal R\subseteq(\mathcal R\mathbin{\bar\otimes}
> \mathcal R)^\omega\cong\mathcal R^\omega$, as in Brown's question.

Sentence M2 after `thm:main` (tex l.82–84):

> In Brown's form, $G_X$ lies in the unitary group of the McDuff factor
> $L(G_X)\mathbin{\bar\otimes}\mathcal R$, which embeds in $\mathcal R^\omega$.

Row T3 of `tab:props` (tex l.212): "$L(G_X)$ is a $\mathrm{II}_1$ factor in $\mathcal R^\omega$ |
infinite conjugacy classes; hyperlinear".

This is the last step of this lane's route. `IsBrownROmegaForm G` bundles the printed conclusions:
`G` is ICC, `L(G)` is a II₁ factor, `L(G) ⊗̄ 𝓡` is McDuff, `G` embeds in the unitary groups of
`L(G)` and of `L(G) ⊗̄ 𝓡`, and for every free ultrafilter `ω` on `ℕ` both `L(G)` (with its trace)
and `L(G) ⊗̄ 𝓡` embed in `𝓡^ω`.

* `isBrownROmegaForm`: every countable, infinite, simple, sofic group has Brown's form
  (`printedBrownFactors`, `exists_groupVonNeumann_embedding`, `exists_tensorHyperfinite_embedding`).
* `brownFormulation_general`: tex l.344–355 for the groups `EL_n(R)` of `thm:general`(b). They are
  LEF (marked limit of finite groups), sofic, hyperlinear, and have Brown's form.
* `brownForm_gx`, `brownForm_el`: sentence M2 for `G_X`, and for `EL_n(LC(X, F₂) ⋊_T ℤ)`, `n ≥ 3`.
* `tabProps_T3`: row T3 for `G_X`.
* `exists_gx_brownForm`: some `G_X`, with `X ⊆ Bool^ℤ` infinite and minimal, is an infinite,
  finitely generated, simple Kazhdan group that is sofic and has Brown's form.

The embeddings are concrete: `𝓡` is the Pauli model and `𝓡^ω` is the tracial ultrapower of the
Pauli model (`Hyperfinite.HyperfiniteUltrapower ω`). The isomorphism `(𝓡 ⊗̄ 𝓡)^ω ≅ 𝓡^ω` is not
stated separately; `exists_tensorHyperfinite_embedding` builds the composite embedding directly.
-/

namespace GroupApproximation.Full.SK06

open SymbolicDynamics.FullShift
open scoped InnerProductSpace

/-- **Brown's form** of a group `G` (tex l.344–355): its nontrivial conjugacy classes are infinite,
`L(G)` is a II₁ factor, `L(G) ⊗̄ 𝓡` is a McDuff factor, `G` embeds in the unitary groups of `L(G)`
and of `L(G) ⊗̄ 𝓡`, and for every free ultrafilter `ω` on `ℕ` there are injective
`⋆`-homomorphisms `L(G) → 𝓡^ω` (carrying the trace `T ↦ ⟪δ₁, T δ₁⟫` to the ultratrace) and
`L(G) ⊗̄ 𝓡 → 𝓡^ω`. -/
def IsBrownROmegaForm (G : Type) [Group G] : Prop :=
  TwoSidedRegularCommutant.IsICC G ∧
    IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra G) ∧
    McDuff.IsMcDuffFactor (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra G)) ∧
    (∃ φ : G →* unitary ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra,
      Function.Injective φ) ∧
    (∃ φ : G →* unitary
        ↥(McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra G)).toStarSubalgebra,
      Function.Injective φ) ∧
    ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      (∃ Φ : ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra →⋆ₐ[ℂ]
          Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ ∧
        ∀ T : ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra,
          Hyperfinite.hyperfiniteUltratrace ω (Φ T)
            = ⟪ReducedGroupCStarTrace.deltaOne G,
                (T : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
                  ReducedGroupCStarTrace.GroupHilbert G) (ReducedGroupCStarTrace.deltaOne G)⟫_ℂ) ∧
      ∃ Φ : ↥(McDuff.tensorHyperfinite
            (GroupVonNeumann.groupVonNeumannAlgebra G)).toStarSubalgebra →⋆ₐ[ℂ]
          Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ

/-- **Brown's formulation for infinite simple sofic groups** (tex l.344–355). A countable,
infinite, simple, sofic group has Brown's form. -/
theorem isBrownROmegaForm {G : Type} [Group G] [Countable G] (hsimple : IsSimpleGroup G)
    (hinf : Infinite G) (hsofic : IsSofic G) : IsBrownROmegaForm G := by
  obtain ⟨hICC, hII, hMcDuff, hψL, hψ⟩ := printedBrownFactors.{0} G hsimple hinf
  unfold IsBrownROmegaForm
  exact ⟨hICC, hII, hMcDuff, hψL, hψ, fun ω hω =>
    ⟨exists_groupVonNeumann_embedding hsofic ω hω, exists_tensorHyperfinite_embedding hsofic ω hω⟩⟩

/-- **Brown's formulation** (tex l.344–355). Let `Λ` act minimally and topologically freely on a
Cantor set `C`, let `R = LC(C, F₂) ⋊ Λ` be generated by a finite set `S ∋ 1`, let `n ≥ 3`, and let
`φ_k : R → M_{N_k}(F₂)` be maps as in `thm:general`(b), with `N_k > 0`. Then `EL_n(R)` is LEF, sofic
and hyperlinear, and it has Brown's form: `L(EL_n(R))` is a II₁ factor that embeds in `𝓡^ω`, and
`EL_n(R)` lies in the unitary group of the McDuff factor `L(EL_n(R)) ⊗̄ 𝓡`, which embeds in
`𝓡^ω`. -/
theorem brownFormulation_general (Λ : Type) [Group Λ] [Group.FG Λ] (C : Type) [TopologicalSpace C]
    [CompactSpace C] [TopologicalSpace.MetrizableSpace C] [TotallyDisconnectedSpace C]
    [PerfectSpace C] [Nonempty C] [MulAction Λ C] [ContinuousConstSMul Λ C]
    (hmin : MulAction.IsMinimal Λ C)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set C, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ C (ZMod 2)))
    (hS1 : (1 : ClopenGroupCrossedProduct Λ C (ZMod 2)) ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ C (ZMod 2))) = ⊤)
    (n : ℕ) (hn : 3 ≤ n) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ C (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hN : ∀ k, 0 < N k) (hφ : SK04.IsPrintedMatricial S N φ) :
    IsLEF ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
      IsSofic ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
      IsHyperlinear ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) ∧
      IsBrownROmegaForm ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) := by
  obtain ⟨⟨hinfG, hfg, hsimple, -⟩, hb⟩ :=
    SK04.printedGeneralTheorem Λ C hmin hfree S hS1 hS n hn
  obtain ⟨hlim, -, hclass, -, -⟩ := hb N φ hN hφ
  have hfin : ∀ k, Finite (Matrix.SpecialLinearGroup (Fin n × Fin (N k)) (ZMod 2)) :=
    fun k => (hclass k).1
  have hLEF : IsLEF ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) :=
    SimpleKazhdanSofic.isLEF_of_isMarkedLimit hfin hlim
  have hsofic := isSofic_of_isLEF hLEF
  haveI : Countable ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ C (ZMod 2))) :=
    GroupApproximation.countable_of_fg hfg
  exact ⟨hLEF, hsofic, isHyperlinear_of_isSofic hsofic, isBrownROmegaForm hsimple hinfG hsofic⟩

/-- **Sentence M2** (tex l.82–84) for `EL_n`, `n ≥ 3`. Let `X` be an infinite minimal subshift over
a finite alphabet. Then `EL_n(LC(X, F₂) ⋊_T ℤ)` has Brown's form. -/
theorem brownForm_el (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S)
    (n : ℕ) (hn : 3 ≤ n) : IsBrownROmegaForm (SK05.EL n S) := by
  obtain ⟨hinfG, hfg, hsimple, -, -, -, hsofic, -⟩ := SK05.main_el A S hinf hmin n hn
  haveI : Countable (SK05.EL n S) := GroupApproximation.countable_of_fg hfg
  exact isBrownROmegaForm hsimple hinfG hsofic

/-- **Sentence M2** (tex l.82–84). Let `X` be an infinite minimal subshift over a finite alphabet.
In Brown's form, `G_X` lies in the unitary group of the McDuff factor `L(G_X) ⊗̄ 𝓡`, which embeds in
`𝓡^ω`. -/
theorem brownForm_gx (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S) :
    McDuff.IsMcDuffFactor (McDuff.tensorHyperfinite
        (GroupVonNeumann.groupVonNeumannAlgebra (SimpleKazhdanSofic.G S))) ∧
      (∃ φ : SimpleKazhdanSofic.G S →* unitary ↥(McDuff.tensorHyperfinite
          (GroupVonNeumann.groupVonNeumannAlgebra (SimpleKazhdanSofic.G S))).toStarSubalgebra,
        Function.Injective φ) ∧
      ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
        ∃ Φ : ↥(McDuff.tensorHyperfinite
              (GroupVonNeumann.groupVonNeumannAlgebra (SimpleKazhdanSofic.G S))).toStarSubalgebra
            →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ := by
  obtain ⟨hinfG, hfg, hsimple, -, -, -, hsofic, -⟩ := SK05.main_printed A S hinf hmin
  haveI : Countable (SimpleKazhdanSofic.G S) := GroupApproximation.countable_of_fg hfg
  obtain ⟨-, -, hMcDuff, -, hψ, hω⟩ := isBrownROmegaForm hsimple hinfG hsofic
  exact ⟨hMcDuff, hψ, fun ω hωfree => (hω ω hωfree).2⟩

/-- **Row T3 of `tab:props`** (tex l.212). Let `X` be an infinite minimal subshift over a finite
alphabet. Then `G_X` has infinite conjugacy classes, and `L(G_X)` is a II₁ factor that embeds in
`𝓡^ω`, preserving the trace, for every free ultrafilter `ω`. -/
theorem tabProps_T3 (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (S : Subshift A ℤ) (hinf : Infinite S.carrier) (hmin : SimpleKazhdanSofic.IsMinimal S) :
    TwoSidedRegularCommutant.IsICC (SimpleKazhdanSofic.G S) ∧
      IIOneFactor.IsIIOneFactor (GroupVonNeumann.groupVonNeumannAlgebra (SimpleKazhdanSofic.G S)) ∧
      ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
        ∃ Φ : ↥(GroupVonNeumann.groupVonNeumannAlgebra (SimpleKazhdanSofic.G S)).toStarSubalgebra
            →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ ∧
          ∀ T : ↥(GroupVonNeumann.groupVonNeumannAlgebra (SimpleKazhdanSofic.G S)).toStarSubalgebra,
            Hyperfinite.hyperfiniteUltratrace ω (Φ T)
              = ⟪ReducedGroupCStarTrace.deltaOne (SimpleKazhdanSofic.G S),
                  (T : ReducedGroupCStarTrace.GroupHilbert (SimpleKazhdanSofic.G S) →L[ℂ]
                    ReducedGroupCStarTrace.GroupHilbert (SimpleKazhdanSofic.G S))
                    (ReducedGroupCStarTrace.deltaOne (SimpleKazhdanSofic.G S))⟫_ℂ := by
  obtain ⟨hinfG, hfg, hsimple, -, -, -, hsofic, -⟩ := SK05.main_printed A S hinf hmin
  haveI : Countable (SimpleKazhdanSofic.G S) := GroupApproximation.countable_of_fg hfg
  obtain ⟨hICC, hII, -, -, -, hω⟩ := isBrownROmegaForm hsimple hinfG hsofic
  exact ⟨hICC, hII, fun ω hωfree => (hω ω hωfree).1⟩

/-- **A group in Brown's form** (tex l.39–53, l.82–84). There is an infinite minimal subshift
`X ⊆ Bool^ℤ` such that `G_X` is an infinite, finitely generated, simple group with property (T),
is sofic, and has Brown's form. -/
theorem exists_gx_brownForm :
    ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ SimpleKazhdanSofic.IsMinimal S ∧
      Infinite (SimpleKazhdanSofic.G S) ∧ Group.FG (SimpleKazhdanSofic.G S) ∧
      IsSimpleGroup (SimpleKazhdanSofic.G S) ∧ HasKazhdanPropertyT.{0, 0} (SimpleKazhdanSofic.G S) ∧
      IsSofic (SimpleKazhdanSofic.G S) ∧ IsBrownROmegaForm (SimpleKazhdanSofic.G S) := by
  obtain ⟨S, hinf, hmin, -⟩ := SK13.every_degree ∅
  obtain ⟨hinfG, hfg, hsimple, hT, -, -, hsofic, -⟩ := SK05.main_printed Bool S hinf hmin
  haveI : Countable (SimpleKazhdanSofic.G S) := GroupApproximation.countable_of_fg hfg
  exact ⟨S, hinf, hmin, hinfG, hfg, hsimple, hT, hsofic, isBrownROmegaForm hsimple hinfG hsofic⟩

end GroupApproximation.Full.SK06

#audit_axioms GroupApproximation.Full.SK06.brownFormulation_general
#audit_axioms GroupApproximation.Full.SK06.brownForm_gx
#audit_axioms GroupApproximation.Full.SK06.tabProps_T3
#audit_axioms GroupApproximation.Full.SK06.exists_gx_brownForm
