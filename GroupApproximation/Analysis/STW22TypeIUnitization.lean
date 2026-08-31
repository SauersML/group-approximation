import GroupApproximation.Analysis.STW22TypeIBlocks
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Type I passes through unitization

This file proves the unitization permanence step in the STW Problem XXII
counterexample's Type-I argument.

The audit's algebra is `A = B⁺` for `B = ⨁_{c₀} D s` non-unital, so the
statement needs a non-unital notion of representation.  `IsTypeINonUnital` is
the GCR condition for `B →⋆ₙₐ[ℂ] (H →L[ℂ] H)`, matching `IsTypeI` clause for
clause.

## The proof

Everything rests on the fact that `A` is spanned by the scalars together with
the image of `B` — `IsScalarExtension ι`, which `Unitization` supplies by
`isScalarExtension_inr`.  Given an irreducible `σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)`, put
`π = σ ∘ ι` and split:

* If `π ≠ 0`, then `π` is irreducible.  The invariance direction is the easy
  one and is exactly where the scalar decomposition is used: a subspace `M`
  invariant under `π` satisfies `σ (l • 1 + ι b) x = l • x + π b x ∈ M`, so it
  is invariant under all of `σ`.  Then `IsTypeINonUnital B` puts every compact
  operator in the range of `π`, hence of `σ`.
* If `π = 0`, then `σ a = l • 1` for every `a`, so *every* closed subspace is
  invariant.  Irreducibility then collapses `H` to a line, on which every
  operator is a scalar and therefore is `σ (c • 1)`.

The second case is isolated as `finrank_one_and_scalar_of_closed_submodules_trivial`,
which is the same computation that proves `isHomogeneousRep_one_complex` in
`Analysis/STW22TypeIBlocks`; it is restated here rather than factored out of the
landed module so that nothing already on `main` has to move.

The countable `c₀`-sum permanence theorem is proved separately in
`Analysis/STW22TypeIC0Sum`.
-/

namespace GroupApproximation
namespace STW22

set_option linter.unusedSectionVars false

noncomputable section

universe u v

/-! ## A space with no proper closed subspaces is a line -/

/-- If a nonzero Hilbert space has no closed subspaces other than `⊥` and `⊤`,
it is one dimensional and every continuous operator on it is a scalar. -/
theorem finrank_one_and_scalar_of_closed_submodules_trivial
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (hne : ∃ v : H, v ≠ 0)
    (htriv : ∀ M : Submodule ℂ H, IsClosed (M : Set H) → M = ⊥ ∨ M = ⊤) :
    Module.finrank ℂ H = 1 ∧ ∀ T : H →L[ℂ] H, ∃ c : ℂ, ∀ x : H, T x = c • x := by
  obtain ⟨v, hv⟩ := hne
  have hspan : Submodule.span ℂ ({v} : Set H) = ⊤ := by
    rcases htriv (Submodule.span ℂ ({v} : Set H))
        (Submodule.span ℂ ({v} : Set H)).closed_of_finiteDimensional with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv
    · exact h
  refine ⟨?_, ?_⟩
  · rw [← finrank_top ℂ H, ← hspan]
    exact finrank_span_singleton hv
  · intro T
    have hTv : T v ∈ Submodule.span ℂ ({v} : Set H) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hTv
    refine ⟨c, fun x => ?_⟩
    have hx : x ∈ Submodule.span ℂ ({v} : Set H) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hd, ContinuousLinearMap.map_smul T d v, ← hc]
    exact smul_comm d c v

/-! ## Non-unital representations and the non-unital GCR condition -/

/-- Topological irreducibility for a representation of a non-unital
C⋆-algebra. -/
def IsIrreducibleNonUnitalRep {B : Type u} [NonUnitalCStarAlgebra B] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  (∃ b : B, π b ≠ 0) ∧
    ∀ M : Submodule ℂ H, IsClosed (M : Set H) → (∀ b : B, ∀ x ∈ M, π b x ∈ M) →
      M = ⊥ ∨ M = ⊤

/-- **Type I (GCR) for a non-unital C⋆-algebra.**  Clause for clause the same
condition as `IsTypeI`, with non-unital `⋆`-homomorphisms. -/
def IsTypeINonUnital (B : Type u) [NonUnitalCStarAlgebra B] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)), IsIrreducibleNonUnitalRep π →
      ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ b : B, π b = T

/-! ## Scalar extensions -/

/-- `A` is a *scalar extension* of `B` along `ι` when every element of `A` is a
scalar multiple of the unit plus an element of the image of `B`.  This is the
only property of the unitization the permanence theorem uses. -/
def IsScalarExtension {B : Type u} [NonUnitalCStarAlgebra B] {A : Type u} [CStarAlgebra A]
    (ι : B →⋆ₙₐ[ℂ] A) : Prop :=
  ∀ a : A, ∃ (l : ℂ) (b : B), a = l • (1 : A) + ι b

/-- The minimal unitization is a scalar extension. -/
theorem isScalarExtension_inr (B : Type u) [NonUnitalCStarAlgebra B] :
    IsScalarExtension (Unitization.inrNonUnitalStarAlgHom ℂ B) := by
  intro a
  refine ⟨a.fst, a.snd, ?_⟩
  have h1 : (a.fst • (1 : Unitization ℂ B)) = Unitization.inl a.fst := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact congrFun (Unitization.algebraMap_eq_inl ℂ B) a.fst
  have h2 : (Unitization.inrNonUnitalStarAlgHom ℂ B) a.snd
      = (a.snd : Unitization ℂ B) := rfl
  rw [h1, h2]
  exact (Unitization.inl_fst_add_inr_snd_eq a).symm

/-! ## The permanence theorem -/

/-- **Type I passes through a scalar extension**, in particular through the
minimal unitization. -/
theorem isTypeI_of_isScalarExtension {B : Type u} [NonUnitalCStarAlgebra B]
    {A : Type u} [CStarAlgebra A] (ι : B →⋆ₙₐ[ℂ] A) (hext : IsScalarExtension ι)
    (h : IsTypeINonUnital.{u, v} B) : IsTypeI.{u, v} A := by
  intro H _ _ _ σ hσ T hT
  obtain ⟨π, hπ⟩ : ∃ π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H), ∀ b : B, π b = σ (ι b) :=
    ⟨(σ.toNonUnitalStarAlgHom).comp ι, fun _ => rfl⟩
  by_cases hzero : ∀ b : B, π b = 0
  · -- `σ` acts by scalars, so `H` is a line and every operator is in the range.
    have hscal : ∀ a : A, ∃ l : ℂ, ∀ x : H, σ a x = l • x := by
      intro a
      obtain ⟨l, b, ha⟩ := hext a
      refine ⟨l, fun x => ?_⟩
      have h1 : σ a = l • (1 : H →L[ℂ] H) := by
        rw [ha, map_add σ, map_smul σ, map_one σ, ← hπ b, hzero b, add_zero]
      rw [h1]
      rfl
    have htriv : ∀ M : Submodule ℂ H, IsClosed (M : Set H) → M = ⊥ ∨ M = ⊤ := by
      intro M hMclosed
      refine hσ.2 M ⟨hMclosed, ?_⟩
      intro a x hx
      obtain ⟨l, hl⟩ := hscal a
      rw [hl x]
      exact M.smul_mem l hx
    obtain ⟨-, hTscal⟩ :=
      finrank_one_and_scalar_of_closed_submodules_trivial hσ.exists_ne_zero htriv
    obtain ⟨c, hc⟩ := hTscal T
    refine ⟨c • (1 : A), ContinuousLinearMap.ext fun x => ?_⟩
    have h2 : σ (c • (1 : A)) = c • (1 : H →L[ℂ] H) := by
      rw [map_smul σ, map_one σ]
    rw [h2, hc x]
    rfl
  · -- `π` is a nonzero irreducible representation of `B`.
    push Not at hzero
    have hirr : IsIrreducibleNonUnitalRep π := by
      refine ⟨hzero, ?_⟩
      intro M hMclosed hMinv
      refine hσ.2 M ⟨hMclosed, ?_⟩
      intro a x hx
      obtain ⟨l, b, ha⟩ := hext a
      have h1 : σ a = l • (1 : H →L[ℂ] H) + π b := by
        rw [ha, map_add σ, map_smul σ, map_one σ, hπ b]
      have h2 : σ a x = l • x + π b x := by
        rw [h1]
        rfl
      rw [h2]
      exact M.add_mem (M.smul_mem l hx) (hMinv b x hx)
    obtain ⟨b, hb⟩ := h H π hirr T hT
    exact ⟨ι b, (hπ b).symm.trans hb⟩

/-- The unitization form, stated at `Unitization ℂ B` itself. -/
theorem isTypeI_unitization {B : Type u} [NonUnitalCStarAlgebra B]
    (h : IsTypeINonUnital.{u, v} B) :
    IsTypeI.{u, v} (Unitization ℂ B) :=
  isTypeI_of_isScalarExtension (Unitization.inrNonUnitalStarAlgHom ℂ B)
    (isScalarExtension_inr B) h

end

end STW22
end GroupApproximation
