import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.GroupModel
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanGeneralClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FiniteModelsBrown.BrownFormulation
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.List
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ↪ R^ω` for the groups of `thm:general`

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":

> (tex 345) Let $G$ be a group as in Theorem~\ref{thm:general}\textup{(b)}.
> (tex 345–348) It is LEF, so it is sofic … and hyperlinear …, and $L(G)$ embeds in
> $\mathcal R^\omega$.

Route.  `printedSimpleKazhdanGeneral` makes `G = EL_n(LC(Z, F₂) ⋊ Λ)` finitely generated, hence
countable (`countable_of_fg`), and `FiniteModelsBrown.manuscriptSentence_lefSoficHyperlinear` makes
it sofic.  `exists_groupVonNeumann_embedding` then gives, for every free ultrafilter `ω` on `ℕ`, an
injective trace-preserving `⋆`-homomorphism `L(G) → R^ω`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open Filter ReducedGroupCStarTrace
open scoped InnerProductSpace

/-- A finitely generated group is countable: it is a quotient of the free group on a finite
generating set. -/
theorem countable_of_fg {G : Type*} [Group G] (h : Group.FG G) : Countable G := by
  classical
  obtain ⟨S, hS⟩ := Group.fg_def.mp h
  have hsurj : Function.Surjective (FreeGroup.lift (fun x : (S : Set G) ↦ (x : G))) := by
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure, Subtype.range_coe]
    exact hS
  haveI : Countable (FreeGroup (S : Set G)) := Quotient.countable
  exact hsurj.countable

/-- **tex 345–348, the embedding `L(G) ↪ R^ω`**: for `G = EL_n(LC(Z, F₂) ⋊ Λ)` as in `thm:general`
and every free ultrafilter `ω` on `ℕ`, there is an injective `⋆`-homomorphism from `L(G)` into the
ultrapower `R^ω` of the hyperfinite II₁ factor, carrying the canonical trace `T ↦ ⟪δ₁, T δ₁⟫` to the
ultratrace. -/
theorem manuscriptSentence_groupVonNeumannEmbedsROmega (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type)
    [TopologicalSpace Z] [CompactSpace Z] [TopologicalSpace.MetrizableSpace Z]
    [TotallyDisconnectedSpace Z] [PerfectSpace Z] [Nonempty Z] [MulAction Λ Z]
    [ContinuousConstSMul Λ Z] (hmin : MulAction.IsMinimal Λ Z)
    (hfree : ∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z)
    (S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2))) (hS1 : 1 ∈ S)
    (hS : Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤) (N : ℕ → ℕ)
    (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2))
    (hφ : IsMatricialVia S N φ) (n : ℕ) (hn : 3 ≤ n) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    ∃ Φ : ↥(GroupVonNeumann.groupVonNeumannAlgebra
          ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))).toStarSubalgebra
        →⋆ₐ[ℂ] Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ ∧
      ∀ T : ↥(GroupVonNeumann.groupVonNeumannAlgebra
          ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))).toStarSubalgebra,
        Hyperfinite.hyperfiniteUltratrace ω (Φ T)
          = ⟪deltaOne ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))),
              (T : GroupHilbert
                  ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2)))
                →L[ℂ] GroupHilbert
                  ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))
              (deltaOne
                ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))))⟫_ℂ := by
  obtain ⟨-, hFG, -⟩ := printedSimpleKazhdanGeneral Λ Z hmin hfree S hS1 hS N φ hφ n hn
  obtain ⟨-, -, hsofic, -⟩ :=
    FiniteModelsBrown.manuscriptSentence_lefSoficHyperlinear Λ Z hmin hfree S hS1 hS N φ hφ n hn
  haveI := countable_of_fg hFG
  exact exists_groupVonNeumann_embedding hsofic ω hω

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.countable_of_fg
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.manuscriptSentence_groupVonNeumannEmbedsROmega
