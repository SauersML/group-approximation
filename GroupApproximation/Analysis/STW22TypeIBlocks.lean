import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Type I (GCR) C⋆-algebras, homogeneous blocks, and the counterexample's step (A5)

Step (A5) of the STW Problem XXII counterexample audit
(`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`)
reads:

> Each `D s` is separable, nuclear and type I; these properties pass through a
> countable `c₀`-sum and unitization.  Hence `A` is separable, unital, nuclear
> and type I.

This file supplies the representation-theoretic definitions that sentence
needs and proves the elementary homogeneous-to-type-I implication used by the
concrete block construction.

## The definitional choice

**Type I is taken in the GCR sense**: every irreducible representation contains
the compact operators in its range.  Concretely, a *representation* of a unital
C⋆-algebra `A` on a complex Hilbert space `H` is a unital `⋆`-algebra
homomorphism `A →⋆ₐ[ℂ] (H →L[ℂ] H)` — Mathlib supplies the C⋆-algebra structure
on `H →L[ℂ] H` (`Analysis/CStarAlgebra/ContinuousLinearMap`) and
`IsCompactOperator` (`Analysis/Normed/Operator/Compact/Basic`), so every piece of
the definition is Mathlib-supported.

*Irreducibility* is topological irreducibility: the only closed invariant
subspaces are `⊥` and `⊤`, and the representation is nonzero.  The nonzero
clause is not decoration: without it the zero representation on a one-dimensional
space would count as irreducible and would refute the GCR condition for every
algebra.

Mathlib has no representation theory of C⋆-algebras — no Jacobson density, no
double commutant, no primitive-ideal space — so the *equivalences* that make
GCR usable (Glimm, Sakai) are unavailable, and so is the classification of the
irreducible representations of `C(X) ⊗ Mₙ`.  What is available, and is used here,
is the elementary implication that a representation whose range is everything
contains the compacts.

## Universes

The carrier of the represented C⋆-algebra and the representation Hilbert
space live in independent universes.  Thus `IsTypeI.{u,v} A` is the literal
GCR condition for representations of `A : Type u` on Hilbert spaces in
`Type v`; every theorem below is polymorphic in `v`.

## What is proved

* `IsHomogeneousRep.isTypeI` — an algebra all of whose irreducible
  representations are surjective is type I.  This is the form in which the
  audit's blocks `D s = Γ(End(1 ⊕ L_s^{⊕s}))` enter: their irreducible
  representations are the fibre evaluations onto `M_(s+1)`.
* `isHomogeneousRep_one_complex` / `isTypeI_complex` — `ℂ` is homogeneous of
  degree one, hence type I, proved directly from the invariant-subspace
  definition.
-/

namespace GroupApproximation
namespace STW22

set_option linter.unusedSectionVars false

noncomputable section

universe u v

/-! ## Representations, invariance, irreducibility -/

section Defs

variable {A : Type u} [CStarAlgebra A] {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A closed subspace of `H` invariant under every operator in the range of the
representation `π`. -/
def IsInvariantSubspace (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : Submodule ℂ H) : Prop :=
  IsClosed (M : Set H) ∧ ∀ a : A, ∀ x ∈ M, π a x ∈ M

/-- **Topological irreducibility.**  A nonzero representation whose only closed
invariant subspaces are `⊥` and `⊤`. -/
def IsIrreducibleRep (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  (∃ a : A, π a ≠ 0) ∧ ∀ M : Submodule ℂ H, IsInvariantSubspace π M → M = ⊥ ∨ M = ⊤

/-- An irreducible representation lives on a nonzero space. -/
theorem IsIrreducibleRep.exists_ne_zero {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (hπ : IsIrreducibleRep π) : ∃ v : H, v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := hπ.1
  refine ha (ContinuousLinearMap.ext fun x => ?_)
  rw [hcon (π a x), hcon ((0 : H →L[ℂ] H) x)]

end Defs

/-! ## Type I in the GCR sense -/

/-- **Type I (GCR).**  Every irreducible representation of `A` has the compact
operators inside its range. -/
def IsTypeI (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), IsIrreducibleRep π →
      ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, π a = T

/-- **`n`-homogeneous.**  Every irreducible representation of `A` is `n`
dimensional and onto — the fibres are exactly `Mₙ`.  This is the audit's
description of `D s = Γ(End(1 ⊕ L_s^{⊕s}))`, with `n = s + 1`. -/
def IsHomogeneousRep (n : ℕ) (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)), IsIrreducibleRep π →
      Module.finrank ℂ H = n ∧ Function.Surjective (π : A → H →L[ℂ] H)

/-- A homogeneous algebra is type I: its irreducible representations are onto,
so a fortiori they contain every compact operator. -/
theorem IsHomogeneousRep.isTypeI {n : ℕ} {A : Type u} [CStarAlgebra A]
    (h : IsHomogeneousRep.{u, v} n A) : IsTypeI.{u, v} A := by
  intro H _ _ _ π hπ T _
  exact (h H π hπ).2 T

/-! ## Model test: `ℂ` is one-homogeneous

Everything below is a computation with the definitions above.  A unital
`⋆`-homomorphism out of `ℂ` sends `c` to `c • 1`, so *every* subspace is
invariant; irreducibility then forces the space to be a line, on which every
operator is a scalar.
-/

theorem isHomogeneousRep_one_complex : IsHomogeneousRep.{0, v} 1 ℂ := by
  intro H _ _ _ π hπ
  have hπc : ∀ (c : ℂ) (x : H), π c x = c • x := by
    intro c x
    have h1 : π c = c • π 1 := by
      rw [← map_smul π c (1 : ℂ), smul_eq_mul, mul_one]
    calc π c x = (c • π 1) x := by rw [h1]
      _ = c • (π 1 x) := rfl
      _ = c • ((1 : H →L[ℂ] H) x) := by rw [map_one π]
      _ = c • x := by rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  have hinv : ∀ M : Submodule ℂ H, ∀ c : ℂ, ∀ x ∈ M, π c x ∈ M := by
    intro M c x hx
    rw [hπc c x]
    exact M.smul_mem c hx
  obtain ⟨v, hv⟩ := hπ.exists_ne_zero
  have hspan : Submodule.span ℂ ({v} : Set H) = ⊤ := by
    rcases hπ.2 (Submodule.span ℂ ({v} : Set H))
        ⟨(Submodule.span ℂ ({v} : Set H)).closed_of_finiteDimensional,
          hinv (Submodule.span ℂ ({v} : Set H))⟩ with h | h
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
    refine ⟨c, ContinuousLinearMap.ext fun x => ?_⟩
    have hx : x ∈ Submodule.span ℂ ({v} : Set H) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hx
    rw [← hd, hπc c (d • v), ContinuousLinearMap.map_smul T d v, ← hc]
    exact smul_comm c d v

theorem isTypeI_complex : IsTypeI.{0, v} ℂ :=
  isHomogeneousRep_one_complex.isTypeI

end

end STW22
end GroupApproximation
