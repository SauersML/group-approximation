import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Entries
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Itinerary
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.Restriction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Sharpness.FlipInvariance
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimpleKazhdanSoficMainClosed
import Mathlib.Topology.Perfect
import Mathlib.Topology.Metrizable.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Sharpness over `ℤ`: simple and Kazhdan iff conjugate to a minimal subshift

`simple_kazhdan_sofic_group.tex`, subsection "Sharpness over $\Z$" (Section `sec:main`),
tex l.393–406:

> For a homeomorphism $T$ of a Cantor set $X$, the group $\EL_3(\LC(X,\F_2)\rtimes_T\Z)$ is simple
> and Kazhdan if and only if $(X,T)$ is conjugate to a minimal subshift. One direction is
> Theorem~\ref{thm:main}. Conversely, [...] so the group is not simple.

and the remark in the introduction, tex l.194–195:

> Over $\Z$ the subshift hypothesis cannot be dropped (Section~\ref{sec:main}).

A Cantor set is given by its topological characterization: a nonempty compact metrizable perfect
totally disconnected Hausdorff space. "Conjugate to a minimal subshift" means a homeomorphism
`φ : X ≃ₜ S` onto a minimal subshift `S ⊆ A^ℤ` over a finite discrete alphabet with
`φ ∘ T = σ ∘ φ`, where `σ = subshiftHomeo S` is the shift.

## Proof route

* One direction is `thm:main` (tex l.396). A conjugacy onto a minimal subshift `S` makes `S`
  infinite, because a nonempty perfect `T₁` space is infinite. The closed root theorem
  `printedSimpleKazhdanSoficMain` then says that `EL₃(R_S)` is simple and Kazhdan, and the
  conjugacy transports both properties (`simpleKazhdan_iff_of_conj_or_flip`).
* Conversely (tex l.397–406): property `(T)` makes the ring finitely generated
  (`kazhdanEntriesGenerateRing`, tex l.397–399). The itinerary map is then a conjugacy onto a
  subshift (`exists_subshift_conj_of_fg`, tex l.400–401). A nonempty proper closed invariant
  subset of the subshift pulls back to one of `X`, which rules out simplicity
  (`not_isSimpleGroup_of_invariant`, tex l.402–406). So the subshift is minimal.

The converse holds for every compact Hausdorff totally disconnected `X`
(`conj_minimalSubshift_of_simpleKazhdan`). Of the Cantor set hypotheses, the proof uses
perfectness and nonemptiness only to make the subshift infinite for `thm:main`. It does not use
metrizability, which is kept in `simpleKazhdanIffMinimalSubshift` so that the statement matches
the printed "Cantor set".
-/

namespace GroupApproximation.Full.SK07

open SymbolicDynamics.FullShift
open GroupApproximation.SimpleKazhdanSofic (subshiftHomeo IsMinimal printedSimpleKazhdanSoficMain)

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
conjugate to it (tex l.402–406, last step: the invariant set lives on the subshift side). -/
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

#audit_axioms isMinimal_of_conj

end Minimal

/-- **"One direction is Theorem~\ref{thm:main}"** (tex l.396). If a nonempty perfect Hausdorff
system `(X, T)` is conjugate to a minimal subshift over a finite alphabet, then
`EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` is simple and has property `(T)`. -/
theorem simpleKazhdan_of_conj_minimalSubshift {X : Type} [TopologicalSpace X] [T2Space X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X) (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [Finite A] (S : Subshift A ℤ) (φ : X ≃ₜ S.carrier) (hmin : IsMinimal S)
    (hφ : ∀ x, φ (T x) = subshiftHomeo S (φ x)) :
    IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) ∧
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) := by
  have hinf : Infinite S.carrier := φ.toEquiv.infinite_iff.mp (infinite_of_perfectSpace X)
  obtain ⟨-, -, hsimple, hT, -⟩ := printedSimpleKazhdanSoficMain A S hinf hmin 3 le_rfl
  exact (simpleKazhdan_iff_of_conj_or_flip (ZMod 2) 3 φ (Or.inl hφ)).mpr ⟨hsimple, hT⟩

#audit_axioms simpleKazhdan_of_conj_minimalSubshift

/-- **"Conversely"** (tex l.397–406). If `EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` is simple and Kazhdan, for a compact
Hausdorff totally disconnected `X`, then `(X, T)` is conjugate to a minimal subshift over a finite
discrete alphabet. -/
theorem conj_minimalSubshift_of_simpleKazhdan {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (hsimple : IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))))
    (hT : HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2)))) :
    ∃ (A : Type) (_ : TopologicalSpace A) (_ : DiscreteTopology A) (_ : Finite A)
      (S : Subshift A ℤ) (φ : X ≃ₜ S.carrier),
      IsMinimal S ∧ ∀ x, φ (T x) = subshiftHomeo S (φ x) := by
  obtain ⟨A, _, _, _, S, φ, hφ⟩ :=
    exists_subshift_conj_of_fg T (kazhdanEntriesGenerateRing (ClopenCrossedProduct T (ZMod 2)) hT)
  exact ⟨A, inferInstance, inferInstance, inferInstance, S, φ,
    isMinimal_of_conj T S φ hφ fun _ hYc hne hproper hY =>
      not_isSimpleGroup_of_invariant T hYc hne hproper hY hsimple, hφ⟩

#audit_axioms conj_minimalSubshift_of_simpleKazhdan

/-- **Sharpness over `ℤ`** (tex l.393–406). For a homeomorphism `T` of a Cantor set `X` (a nonempty
compact metrizable perfect totally disconnected Hausdorff space), `EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` is simple
and Kazhdan if and only if `(X, T)` is conjugate to a minimal subshift over a finite alphabet. -/
theorem simpleKazhdanIffMinimalSubshift {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [TopologicalSpace.MetrizableSpace X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X) :
    (IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) ∧
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2)))) ↔
      ∃ (A : Type) (_ : TopologicalSpace A) (_ : DiscreteTopology A) (_ : Finite A)
        (S : Subshift A ℤ) (φ : X ≃ₜ S.carrier),
        IsMinimal S ∧ ∀ x, φ (T x) = subshiftHomeo S (φ x) := by
  constructor
  · rintro ⟨hsimple, hT⟩
    exact conj_minimalSubshift_of_simpleKazhdan T hsimple hT
  · rintro ⟨A, _, _, _, S, φ, hmin, hφ⟩
    exact simpleKazhdan_of_conj_minimalSubshift T A S φ hmin hφ

#audit_axioms simpleKazhdanIffMinimalSubshift

/-- **"Over $\Z$ the subshift hypothesis cannot be dropped"** (tex l.194–195). For a homeomorphism
`T` of a compact Hausdorff totally disconnected space (in particular of a Cantor set) that is not
conjugate to a minimal subshift over a finite alphabet, `EL₃(LC(X, 𝔽₂) ⋊_T ℤ)` is not both simple
and Kazhdan. So the conclusion of `thm:main` fails for every such system. -/
theorem subshiftHypothesisCannotBeDropped {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (hnot : ¬ ∃ (A : Type) (_ : TopologicalSpace A) (_ : DiscreteTopology A) (_ : Finite A)
      (S : Subshift A ℤ) (φ : X ≃ₜ S.carrier),
      IsMinimal S ∧ ∀ x, φ (T x) = subshiftHomeo S (φ x)) :
    ¬ (IsSimpleGroup (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2))) ∧
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) (ClopenCrossedProduct T (ZMod 2)))) :=
  fun h => hnot (conj_minimalSubshift_of_simpleKazhdan T h.1 h.2)

#audit_axioms subshiftHypothesisCannotBeDropped

end GroupApproximation.Full.SK07
