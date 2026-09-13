/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.Toeplitz.FockSpace
import GroupApproximation.Toeplitz.Sections
import Mathlib.Topology.ContinuousMap.Defs

/-!
# The Fock module of a set of sections

For a set `E` of bounded sections `X → ℓ²(ι)`, `fockModule E` is the closed linear span of the
sections `ζ₁ ⊗ ⋯ ⊗ ζ_m ⊗ f` with `ζ_i ∈ E` and `f ∈ C(X)`, realised fibrewise in the Fock space
`ℓ²(List ι)`.  This is the module `F(E)` of Blanchard, arXiv:1507.02535v1, Definition 5.1 (p. 7),
in the form used by `Palomar/BlanchardToeplitzChallenge.lean`.

The creation operator `creationSec ζ` preserves `fockModule E` when `ζ ∈ E`
(`creationSec_mem_fockModule`).  The annihilation operator `annihilationSec ζ` preserves it when
`x ↦ ⟪ζ x, ζ' x⟫` is continuous for every `ζ' ∈ E` (`annihilationSec_mem_fockModule`).  Their
restrictions to `fockModule E` are adjoint at every point (`isSectionAdjoint_creationEnd`).
-/

namespace GroupApproximation.Toeplitz

noncomputable section

open scoped ENNReal InnerProductSpace

variable {X : Type*} {ι : Type*}

/-- The sections `ζ₁ ⊗ ⋯ ⊗ ζ_m ⊗ f` of `E^{⊗m}`, `ζ_i ∈ E`, `f ∈ C(X)`. -/
def fockGenerators [TopologicalSpace X] [DecidableEq ι] (E : Set (Sections X (Fib ι))) :
    ℕ → Set (Sections X (Fock ι))
  | 0 => {ω | ∃ f : C(X, ℂ), ∀ x w, (ω x : List ι → ℂ) w = if w = [] then f x else 0}
  | m + 1 => {ω | ∃ ζ ∈ E, ∃ ω' ∈ fockGenerators E m, ∀ x w,
      (ω x : List ι → ℂ) w = tensorCoord (ζ x : ι → ℂ) (ω' x : List ι → ℂ) w}

theorem mem_fockGenerators_zero [TopologicalSpace X] [DecidableEq ι] {E : Set (Sections X (Fib ι))}
    {ω : Sections X (Fock ι)} :
    ω ∈ fockGenerators E 0 ↔
      ∃ f : C(X, ℂ), ∀ x w, (ω x : List ι → ℂ) w = if w = [] then f x else 0 :=
  Iff.rfl

theorem mem_fockGenerators_succ [TopologicalSpace X] [DecidableEq ι] {E : Set (Sections X (Fib ι))}
    {m : ℕ} {ω : Sections X (Fock ι)} :
    ω ∈ fockGenerators E (m + 1) ↔ ∃ ζ ∈ E, ∃ ω' ∈ fockGenerators E m, ∀ x w,
      (ω x : List ι → ℂ) w = tensorCoord (ζ x : ι → ℂ) (ω' x : List ι → ℂ) w :=
  Iff.rfl

/-- The Fock module `F(E) = ⊕_m E^{⊗m}` (Blanchard, Definition 5.1, p. 7). -/
def fockModule [TopologicalSpace X] [DecidableEq ι] (E : Set (Sections X (Fib ι))) :
    Submodule ℂ (Sections X (Fock ι)) :=
  (Submodule.span ℂ (⋃ m, fockGenerators E m)).topologicalClosure

theorem mem_fockModule_of_mem_fockGenerators [TopologicalSpace X] [DecidableEq ι]
    {E : Set (Sections X (Fib ι))} {m : ℕ} {ω : Sections X (Fock ι)}
    (hω : ω ∈ fockGenerators E m) : ω ∈ fockModule E :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_iUnion.2 ⟨m, hω⟩))

/-- `S` is the adjoint of `T`: `⟪T ξ, η⟫ = ⟪ξ, S η⟫` at every point. -/
def IsSectionAdjoint {M : Submodule ℂ (Sections X (Fock ι))} (T S : Module.End ℂ M) : Prop :=
  ∀ ξ η : M, ∀ x, ⟪((T ξ : M) : Sections X (Fock ι)) x, (η : Sections X (Fock ι)) x⟫_ℂ =
    ⟪(ξ : Sections X (Fock ι)) x, ((S η : M) : Sections X (Fock ι)) x⟫_ℂ

/-- The creation operator `ω ↦ ζ ⊗ ω` on sections. -/
def creationSec (ζ : Sections X (Fib ι)) : Sections X (Fock ι) →L[ℂ] Sections X (Fock ι) :=
  fibrewise (fun x => creation (ζ x)) (norm_nonneg ζ) fun x =>
    (norm_creation_le _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero ζ x)

theorem creationSec_apply (ζ : Sections X (Fib ι)) (ω : Sections X (Fock ι)) (x : X) :
    creationSec ζ ω x = creation (ζ x) (ω x) := rfl

/-- The annihilation operator on sections, fibrewise adjoint to `creationSec ζ`. -/
def annihilationSec (ζ : Sections X (Fib ι)) : Sections X (Fock ι) →L[ℂ] Sections X (Fock ι) :=
  fibrewise (fun x => annihilation (ζ x)) (norm_nonneg ζ) fun x =>
    (norm_annihilation_le _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero ζ x)

theorem annihilationSec_apply (ζ : Sections X (Fib ι)) (ω : Sections X (Fock ι)) (x : X) :
    annihilationSec ζ ω x = annihilation (ζ x) (ω x) := rfl

theorem norm_inner_apply_le (ζ ζ' : Sections X (Fib ι)) (x : X) :
    ‖⟪ζ x, ζ' x⟫_ℂ‖ ≤ ‖ζ‖ * ‖ζ'‖ :=
  (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero ζ x)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero ζ' x) (norm_nonneg _) (norm_nonneg _))

/-- Generators are closed under multiplication by bounded continuous functions. -/
theorem smulSec_mem_fockGenerators [TopologicalSpace X] [DecidableEq ι]
    {E : Set (Sections X (Fib ι))} {h : X → ℂ} (hh : Continuous h) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) :
    ∀ m, ∀ ω ∈ fockGenerators E m, smulSec h hB ω ∈ fockGenerators E m := by
  intro m
  induction m with
  | zero =>
    intro ω hω
    obtain ⟨f, hf⟩ := mem_fockGenerators_zero.1 hω
    refine mem_fockGenerators_zero.2 ⟨⟨fun x => h x * f x, hh.mul f.continuous⟩, fun x w => ?_⟩
    simp only [smulSec_apply, lp.coeFn_smul, Pi.smul_apply, hf x w, smul_eq_mul, mul_ite, mul_zero,
      ContinuousMap.coe_mk]
  | succ m ih =>
    intro ω hω
    obtain ⟨ζ, hζ, ω', hω', hω⟩ := mem_fockGenerators_succ.1 hω
    refine mem_fockGenerators_succ.2 ⟨ζ, hζ, smulSec h hB ω', ih ω' hω', fun x w => ?_⟩
    cases w with
    | nil =>
      simp only [smulSec_apply, lp.coeFn_smul, Pi.smul_apply, hω x [], smul_eq_mul, tensorCoord_nil,
        mul_zero]
    | cons i w =>
      simp only [smulSec_apply, lp.coeFn_smul, Pi.smul_apply, hω x (i :: w), smul_eq_mul,
        tensorCoord_cons]
      ring

theorem creationSec_mem_fockGenerators [TopologicalSpace X] [DecidableEq ι]
    {E : Set (Sections X (Fib ι))} {ζ : Sections X (Fib ι)} (hζ : ζ ∈ E) {m : ℕ}
    {ω : Sections X (Fock ι)} (hω : ω ∈ fockGenerators E m) :
    creationSec ζ ω ∈ fockGenerators E (m + 1) :=
  mem_fockGenerators_succ.2 ⟨ζ, hζ, ω, hω, fun _ _ => rfl⟩

theorem creationSec_mem_fockModule [TopologicalSpace X] [DecidableEq ι]
    {E : Set (Sections X (Fib ι))} {ζ : Sections X (Fib ι)} (hζ : ζ ∈ E) :
    ∀ ω ∈ fockModule E, creationSec ζ ω ∈ fockModule E :=
  mem_topologicalClosure_span_of_forall _ _ fun ω hω => by
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hω
    exact mem_fockModule_of_mem_fockGenerators (creationSec_mem_fockGenerators hζ hm)

theorem annihilationSec_eq_zero [TopologicalSpace X] [DecidableEq ι]
    {E : Set (Sections X (Fib ι))} (ζ : Sections X (Fib ι)) {ω : Sections X (Fock ι)}
    (hω : ω ∈ fockGenerators E 0) : annihilationSec ζ ω = 0 := by
  obtain ⟨f, hf⟩ := mem_fockGenerators_zero.1 hω
  refine lp.ext (funext fun x => ?_)
  show annihilation (ζ x) (ω x) = 0
  refine annihilation_eq_zero (ζ x) (ω x) fun i w => ?_
  rw [hf x (i :: w), if_neg (List.cons_ne_nil i w)]

theorem annihilationSec_eq_smulSec {ζ ζ' : Sections X (Fib ι)} {ω ω' : Sections X (Fock ι)}
    (hω : ∀ x w, (ω x : List ι → ℂ) w = tensorCoord (ζ' x : ι → ℂ) (ω' x : List ι → ℂ) w) :
    annihilationSec ζ ω = smulSec (fun x => ⟪ζ x, ζ' x⟫_ℂ) (norm_inner_apply_le ζ ζ') ω' := by
  refine lp.ext (funext fun x => ?_)
  have hx : ω x = creation (ζ' x) (ω' x) := lp.ext (funext (hω x))
  show annihilation (ζ x) (ω x) = ⟪ζ x, ζ' x⟫_ℂ • ω' x
  rw [hx, annihilation_creation]

theorem annihilationSec_mem_fockModule [TopologicalSpace X] [DecidableEq ι]
    {E : Set (Sections X (Fib ι))} {ζ : Sections X (Fib ι)}
    (hcont : ∀ ζ' ∈ E, Continuous fun x => ⟪ζ x, ζ' x⟫_ℂ) :
    ∀ ω ∈ fockModule E, annihilationSec ζ ω ∈ fockModule E :=
  mem_topologicalClosure_span_of_forall _ _ fun ω hω => by
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hω
    cases m with
    | zero =>
      rw [annihilationSec_eq_zero ζ hm]
      exact Submodule.zero_mem _
    | succ m =>
      obtain ⟨ζ', hζ', ω', hω', hω⟩ := mem_fockGenerators_succ.1 hm
      rw [annihilationSec_eq_smulSec hω]
      exact mem_fockModule_of_mem_fockGenerators
        (smulSec_mem_fockGenerators (hcont ζ' hζ') _ m ω' hω')

/-- The restriction of `creationSec ζ` to an invariant submodule. -/
def creationEnd {M : Submodule ℂ (Sections X (Fock ι))} (ζ : Sections X (Fib ι))
    (hM : ∀ ω ∈ M, creationSec ζ ω ∈ M) : Module.End ℂ M :=
  restrictEnd (creationSec ζ) M hM

/-- The restriction of `annihilationSec ζ` to an invariant submodule. -/
def annihilationEnd {M : Submodule ℂ (Sections X (Fock ι))} (ζ : Sections X (Fib ι))
    (hM : ∀ ω ∈ M, annihilationSec ζ ω ∈ M) : Module.End ℂ M :=
  restrictEnd (annihilationSec ζ) M hM

theorem creationEnd_apply {M : Submodule ℂ (Sections X (Fock ι))} (ζ : Sections X (Fib ι))
    (hM : ∀ ω ∈ M, creationSec ζ ω ∈ M) (ω : M) (x : X) :
    ((creationEnd ζ hM ω : M) : Sections X (Fock ι)) x =
      creation (ζ x) ((ω : Sections X (Fock ι)) x) := rfl

theorem annihilationEnd_apply {M : Submodule ℂ (Sections X (Fock ι))} (ζ : Sections X (Fib ι))
    (hM : ∀ ω ∈ M, annihilationSec ζ ω ∈ M) (ω : M) (x : X) :
    ((annihilationEnd ζ hM ω : M) : Sections X (Fock ι)) x =
      annihilation (ζ x) ((ω : Sections X (Fock ι)) x) := rfl

theorem isSectionAdjoint_creationEnd {M : Submodule ℂ (Sections X (Fock ι))}
    (ζ : Sections X (Fib ι)) (hC : ∀ ω ∈ M, creationSec ζ ω ∈ M)
    (hD : ∀ ω ∈ M, annihilationSec ζ ω ∈ M) :
    IsSectionAdjoint (creationEnd ζ hC) (annihilationEnd ζ hD) := fun ω ω' x => by
  rw [creationEnd_apply, annihilationEnd_apply]
  exact (inner_annihilation_right (ζ x) _ _).symm

end

end GroupApproximation.Toeplitz
