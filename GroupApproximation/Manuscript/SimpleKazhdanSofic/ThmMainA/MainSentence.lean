import GroupApproximation.Manuscript.SimpleKazhdanSofic.ThmMainA.MarkedGroups
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.McDuffBrownFormulation
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MinimalDenseOrbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Theorem `thm:main`: the main clause, Brown's form, minimal subshifts (tex l.76–86)

`simple_kazhdan_sofic_group.tex`, Theorem `thm:main` and the paragraph after it:

> (l.76–78) [For an infinite minimal subshift $X$ over a finite alphabet, $G_X$] is an infinite,
> finitely generated, simple group with Kazhdan's property~\textup{(T)}, and an expander limit, in
> the sense defined below, of finite simple groups $\SL_{3N}(\F_2)$.
>
> (l.82–84) In Brown's form, $G_X$ lies in the unitary group of the McDuff factor
> $L(G_X)\mathbin{\bar\otimes}\mathcal R$, which embeds in $\mathcal R^\omega$
> (Section~\ref{sec:proof}).
>
> (l.86) Here $X$ is a closed shift-invariant set in which every orbit is dense.

## Proof routes

* `manuscriptSentence_gXInfiniteFGSimpleKazhdanExpanderLimit`: the closed corpus theorem
  `printedSimpleKazhdanSoficMain` at `n = 3` gives infiniteness, finite generation, simplicity,
  property (T) and a marked limit with a family of expanders of the simple groups
  `SL_{3 × N}(F₂)`.  `ThmMainA.isExpanderLimit_of_isMarkedLimit` converts that limit into the printed
  expander-limit notion of tex l.92–100, so `G_X` is an expander limit of the class
  `IsFiniteSimpleSLThreeN` of finite simple groups isomorphic to some `SL_{3N}(F₂)`.
* `manuscriptSentence_brownFormGXUnitaryMcDuff`: `printedBrownFormulationFactors` applied to the
  infinite simple group `G_X`: `L(G_X) ⊗̄ R` is a McDuff factor and `G_X` embeds in its unitary group.
  The embedding `L(G_X) ⊗̄ R ↪ R^ω` is not formalized in the corpus, so this row is partial.
* `manuscriptSentence_minimalSubshiftClosedInvariantDenseOrbits`: a subshift is closed and
  shift-invariant (fields of `Subshift`).  Minimality, which has no nonempty proper closed invariant
  subset, is equivalent to density of every orbit.  Forward: `minimalSubshift_dense_orbits`.
  Backward: a nonempty closed invariant `C ⊆ X` contains the orbit of one of its points.  That orbit
  is dense, and `C` is closed, so `C = X`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ThmMainA

open SymbolicDynamics.FullShift Set

/-- The class of **finite simple groups `SL_{3N}(F₂)`** (tex l.78): finite simple groups isomorphic
to a special linear group over `F₂` of size `3N`. -/
def IsFiniteSimpleSLThreeN (Q : Type) [Group Q] : Prop :=
  Finite Q ∧ IsSimpleGroup Q ∧
    ∃ (N : ℕ) (n : Type) (_ : Fintype n) (_ : DecidableEq n), Fintype.card n = 3 * N ∧
      Nonempty (Q ≃* Matrix.SpecialLinearGroup n (ZMod 2))

/-- **tex l.76–78 (Theorem `thm:main`).** For an infinite minimal subshift `X` over a finite
alphabet, `G_X = EL₃(LC(X, F₂) ⋊ ℤ)` is an infinite, finitely generated, simple group with Kazhdan's
property (T), and an expander limit (tex l.92–100) of finite simple groups `SL_{3N}(F₂)`. -/
theorem manuscriptSentence_gXInfiniteFGSimpleKazhdanExpanderLimit (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    Infinite (G S) ∧ Group.FG (G S) ∧ IsSimpleGroup (G S) ∧ HasKazhdanPropertyT.{0, 0} (G S) ∧
      IsExpanderLimitOfClass IsFiniteSimpleSLThreeN (G S) := by
  obtain ⟨hinfG, hfg, hsimple, hT, hlimit, -, -, -⟩ :=
    printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  refine ⟨hinfG, hfg, hsimple, hT, ?_⟩
  obtain ⟨_, _, N, _, hsimpleSL, hlim, hexp⟩ := hlimit
  obtain ⟨m, g, q, hq⟩ := isExpanderLimit_of_isMarkedLimit hlim hexp
  have hclass : ∀ ℓ, IsFiniteSimpleSLThreeN
      (Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2)) := by
    intro ℓ
    refine ⟨inferInstance, hsimpleSL ℓ, N ℓ, Fin 3 × Fin (N ℓ), inferInstance, inferInstance, ?_,
      ⟨MulEquiv.refl _⟩⟩
    show Fintype.card (Fin 3 × Fin (N ℓ)) = 3 * N ℓ
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  exact ⟨m, g, fun ℓ => Matrix.SpecialLinearGroup (Fin 3 × Fin (N ℓ)) (ZMod 2),
    fun ℓ => inferInstance, q, hclass, hq⟩

/-- **tex l.82–84 (Brown's form), the part closed in the corpus.** For `G_X` as in `thm:main`, the
tensor product `L(G_X) ⊗̄ R` is a McDuff factor, and `G_X` embeds as a subgroup of its unitary group.
The further embedding `L(G_X) ⊗̄ R ↪ R^ω` is not formalized. -/
theorem manuscriptSentence_brownFormGXUnitaryMcDuff (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (hinf : Infinite S.carrier)
    (hmin : IsMinimal S) :
    McDuff.IsMcDuffFactor
        (McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra (G S))) ∧
      ∃ φ : G S →* unitary
          ↥(McDuff.tensorHyperfinite (GroupVonNeumann.groupVonNeumannAlgebra (G S))).toStarSubalgebra,
        Function.Injective φ := by
  obtain ⟨hinfG, -, hsimple, -⟩ := printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  obtain ⟨-, hMcDuff, hφ⟩ := printedBrownFormulationFactors.{0} (G S) hsimple hinfG
  exact ⟨hMcDuff, hφ⟩

/-- **tex l.86.** *Here `X` is a closed shift-invariant set in which every orbit is dense.*  A
subshift is closed and shift-invariant, and it is minimal exactly when every orbit of the shift is
dense. -/
theorem manuscriptSentence_minimalSubshiftClosedInvariantDenseOrbits {A : Type}
    [TopologicalSpace A] (S : Subshift A ℤ) :
    IsClosed S.carrier ∧ (∀ g : ℤ, MapsTo (shift g) S.carrier S.carrier) ∧
      (IsMinimal S ↔ ∀ x : S.carrier, Dense (Set.range fun j : ℤ => (subshiftHomeo S ^ j) x)) := by
  refine ⟨S.isClosed, S.mapsTo, ⟨fun hmin x => minimalSubshift_dense_orbits S hmin x, ?_⟩⟩
  intro hdense C hC hCX hinv
  rcases C.eq_empty_or_nonempty with hempty | ⟨c, hc⟩
  · exact Or.inl hempty
  · right
    have hsub : Set.range (fun j : ℤ => (subshiftHomeo S ^ j) ⟨c, hCX hc⟩) ⊆
        Subtype.val ⁻¹' C := by
      rintro _ ⟨j, rfl⟩
      show ((subshiftHomeo S ^ j) ⟨c, hCX hc⟩).1 ∈ C
      rw [subshiftHomeo_zpow_apply]
      exact hinv j hc
    have hclosed := closure_minimal hsub (hC.preimage continuous_subtype_val)
    rw [(hdense ⟨c, hCX hc⟩).closure_eq] at hclosed
    exact Set.Subset.antisymm hCX fun y hy => hclosed (Set.mem_univ (⟨y, hy⟩ : S.carrier))

end ThmMainA
end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.manuscriptSentence_gXInfiniteFGSimpleKazhdanExpanderLimit
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.manuscriptSentence_brownFormGXUnitaryMcDuff
#audit_axioms GroupApproximation.SimpleKazhdanSofic.ThmMainA.manuscriptSentence_minimalSubshiftClosedInvariantDenseOrbits
