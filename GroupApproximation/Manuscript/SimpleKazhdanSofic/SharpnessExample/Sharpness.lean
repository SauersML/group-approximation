import GroupApproximation.Manuscript.SimpleKazhdanSofic.SharpnessExample.RingFromGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SharpnessExample.Itinerary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SharpnessExample.Restriction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import GroupApproximation.Manuscript.SimpleKazhdanSofic.CrossedProductConjugacy
import Mathlib.Topology.Perfect
import Mathlib.Topology.Metrizable.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Sharpness over `ℤ`

`simple_kazhdan_sofic_group.tex`, subsection "Sharpness over $\Z$", l.394–397:

> For a homeomorphism $T$ of a Cantor set $X$, the group $\EL_3(\LC(X,\F_2)\rtimes_T\Z)$ is simple
> and Kazhdan if and only if $(X,T)$ is conjugate to a minimal subshift. One direction is
> Theorem~\ref{thm:main}.

A Cantor set is spelled by its topological characterization: a nonempty compact metrizable perfect
totally disconnected (Hausdorff) space.  "Conjugate to a minimal subshift" means a homeomorphism
`φ : X ≃ₜ S` onto a minimal subshift `S ⊆ A^ℤ` over a finite discrete alphabet with
`φ ∘ T = σ ∘ φ`, `σ` the shift `subshiftHomeo S`.

## Proof route

* `manuscriptSentence_oneDirectionIsMain` (tex l.396): a conjugacy to a minimal subshift `S` makes
  `S` infinite (a perfect nonempty `T₁` space is infinite), so the corpus `thm:main`
  (`printedSimpleKazhdanSoficMain`, closed) gives that `EL₃(R S)` is simple and Kazhdan; the
  conjugacy gives `EL₃(R_T) ≃* EL₃(R S)` (`nonempty_elementaryGroup_equiv_of_conj_or_flip`), and
  both properties transfer along isomorphisms.
* Conversely (tex l.397–406): property `(T)` makes the ring finitely generated
  (`exists_finset_subring_closure_eq_top_of_kazhdan`), the itinerary map is a conjugacy onto a
  subshift (`exists_subshift_conj_of_fg`), and a nonempty proper closed invariant subset of the
  subshift pulls back to one of `X`, which forbids simplicity (`not_isSimpleGroup_of_invariant`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SharpnessExample

open SymbolicDynamics.FullShift

/-- A nonempty perfect `T₁` space is infinite: a finite `T₁` space is discrete, so its points are
isolated. -/
theorem infinite_of_perfectSpace (X : Type) [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    [Nonempty X] : Infinite X := by
  rw [← not_finite_iff_infinite]
  intro _hfin
  obtain ⟨x⟩ := ‹Nonempty X›
  have hacc : AccPt x (Filter.principal Set.univ) :=
    PerfectSpace.univ_preperfect x (Set.mem_univ x)
  obtain ⟨y, ⟨hy, _⟩, hyx⟩ :=
    accPt_iff_nhds.mp hacc {x} ((isOpen_discrete ({x} : Set X)).mem_nhds (Set.mem_singleton x))
  exact hyx hy

section Minimal

variable {X : Type} [TopologicalSpace X] (T : X ≃ₜ X)

/-- If `(X, T)` has no nonempty proper closed invariant subset, then neither has a subshift
conjugate to it. -/
theorem isMinimal_of_conj {A : Type} [TopologicalSpace A] (S : Subshift A ℤ)
    (φ : X ≃ₜ S.carrier) (hφ : ∀ x, φ (T x) = subshiftHomeo S (φ x))
    (h : ∀ Y : Set X, IsClosed Y → Y.Nonempty → Y ≠ Set.univ → T '' Y = Y → False) :
    IsMinimal S := by
  have hstep : ∀ x, ((φ (T x) : S.carrier) : ℤ → A) = shift 1 ((φ x : S.carrier) : ℤ → A) :=
    fun x => congrArg Subtype.val (hφ x)
  have hback : ∀ w : ℤ → A, shift (-1) (shift 1 w) = w := fun w => by
    funext n
    show w (1 + (-1 + n)) = w n
    exact congrArg w (by omega)
  intro C hC hCS hinv
  rcases Set.eq_empty_or_nonempty C with hempty | ⟨c, hc⟩
  · exact Or.inl hempty
  refine Or.inr (Set.Subset.antisymm hCS fun z hz => ?_)
  by_contra hzC
  refine h {x | ((φ x : S.carrier) : ℤ → A) ∈ C}
    (IsClosed.preimage (continuous_subtype_val.comp φ.continuous) hC)
    ⟨φ.symm ⟨c, hCS hc⟩, ?_⟩ ?_ ?_
  · show ((φ (φ.symm ⟨c, hCS hc⟩) : S.carrier) : ℤ → A) ∈ C
    rw [Homeomorph.apply_symm_apply]
    exact hc
  · intro huniv
    have hx : ((φ (φ.symm ⟨z, hz⟩) : S.carrier) : ℤ → A) ∈ C :=
      Set.eq_univ_iff_forall.mp huniv (φ.symm ⟨z, hz⟩)
    rw [Homeomorph.apply_symm_apply] at hx
    exact hzC hx
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show ((φ (T x) : S.carrier) : ℤ → A) ∈ C
      rw [hstep x]
      exact hinv 1 (show ((φ x : S.carrier) : ℤ → A) ∈ C from hx)
    · intro x hx
      refine ⟨T.symm x, ?_, T.apply_symm_apply x⟩
      show ((φ (T.symm x) : S.carrier) : ℤ → A) ∈ C
      have h1 := hinv (-1) (show ((φ (T (T.symm x)) : S.carrier) : ℤ → A) ∈ C by
        rw [Homeomorph.apply_symm_apply]
        exact hx)
      rwa [hstep, hback] at h1

end Minimal

/-- **Sentence l.396 (tex l.396–397), one direction is `thm:main`.** If a nonempty perfect
compact Hausdorff system `(X, T)` is conjugate to a minimal subshift over a finite alphabet, then
`EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` is simple and has property `(T)`. -/
theorem manuscriptSentence_oneDirectionIsMain {X : Type} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X) (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (φ : X ≃ₜ S.carrier) (hmin : IsMinimal S)
    (hφ : ∀ x, φ (T x) = subshiftHomeo S (φ x)) :
    IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) ∧
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) := by
  have hinf : Infinite S.carrier := φ.toEquiv.infinite_iff.mp (infinite_of_perfectSpace X)
  obtain ⟨-, -, hsimple, hT, -⟩ := printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  obtain ⟨e⟩ := nonempty_elementaryGroup_equiv_of_conj_or_flip (ZMod 2) 3 φ (Or.inl hφ)
  haveI := hsimple
  exact ⟨e.isSimpleGroup, HasKazhdanPropertyT.of_mulEquiv e hT⟩

#audit_axioms manuscriptSentence_oneDirectionIsMain

/-- **Sentence l.394 (tex l.394–396).** For a homeomorphism `T` of a Cantor set `X` (a nonempty
compact metrizable perfect totally disconnected space), `EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` is simple and
Kazhdan if and only if `(X, T)` is conjugate to a minimal subshift over a finite alphabet. -/
theorem manuscriptSentence_simpleKazhdanIffMinimalSubshift {X : Type} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [TopologicalSpace.MetrizableSpace X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X) :
    (IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) ∧
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2)))) ↔
      ∃ (A : Type) (_ : TopologicalSpace A) (_ : DiscreteTopology A) (_ : Finite A)
        (S : Subshift A ℤ) (φ : X ≃ₜ S.carrier),
        IsMinimal S ∧ ∀ x, φ (T x) = subshiftHomeo S (φ x) := by
  constructor
  · rintro ⟨hsimple, hT⟩
    obtain ⟨A, _, _, _, S, φ, hφ⟩ := exists_subshift_conj_of_fg T
      (exists_finset_subring_closure_eq_top_of_kazhdan (ClopenCrossedProduct T (ZMod 2)) hT)
    refine ⟨A, inferInstance, inferInstance, inferInstance, S, φ,
      isMinimal_of_conj T S φ hφ fun Y hYc hne hproper hY => ?_, hφ⟩
    exact not_isSimpleGroup_of_invariant T hYc hne hproper hY hsimple
  · rintro ⟨A, _, _, _, S, φ, hmin, hφ⟩
    exact manuscriptSentence_oneDirectionIsMain T A S φ hmin hφ

#audit_axioms manuscriptSentence_simpleKazhdanIffMinimalSubshift

end GroupApproximation.SimpleKazhdanSofic.SharpnessExample
