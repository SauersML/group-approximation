/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Fibrewise operators on bounded sections

`Sections X V` is the space of bounded maps `X → V` with the supremum norm.  A uniformly bounded
family `L x` of operators on `V` acts on sections fibrewise (`fibrewise`).  An operator that maps a
set `S` of sections into the closed linear span of `S` preserves that closed span
(`mem_topologicalClosure_span_of_forall`), and then restricts to an endomorphism of it
(`restrictEnd`).
-/

namespace GroupApproximation.Toeplitz

noncomputable section

open scoped ENNReal

variable {X : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Bounded sections `X → V` with the supremum norm. -/
abbrev Sections (X : Type*) (V : Type*) [NormedAddCommGroup V] : Type _ := lp (fun _ : X => V) ∞

theorem norm_fibrewise_le (L : X → V →L[ℂ] V) {B : ℝ} (hB : ∀ x, ‖L x‖ ≤ B)
    (ξ : Sections X V) (x : X) : ‖L x (ξ x)‖ ≤ B * ‖ξ‖ :=
  ((L x).le_opNorm_of_le (lp.norm_apply_le_norm ENNReal.top_ne_zero ξ x)).trans
    (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))

theorem memℓp_fibrewise (L : X → V →L[ℂ] V) {B : ℝ} (hB : ∀ x, ‖L x‖ ≤ B) (ξ : Sections X V) :
    Memℓp (fun x => L x (ξ x)) ∞ := by
  refine memℓp_infty ⟨B * ‖ξ‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact norm_fibrewise_le L hB ξ x

/-- The fibrewise action of a uniformly bounded family of operators, as a linear map. -/
def fibrewiseL (L : X → V →L[ℂ] V) {B : ℝ} (hB : ∀ x, ‖L x‖ ≤ B) :
    Sections X V →ₗ[ℂ] Sections X V where
  toFun ξ := ⟨fun x => L x (ξ x), memℓp_fibrewise L hB ξ⟩
  map_add' ξ η := lp.ext <| funext fun x => by
    show L x ((ξ + η) x) = L x (ξ x) + L x (η x)
    rw [lp.coeFn_add, Pi.add_apply, map_add]
  map_smul' c ξ := lp.ext <| funext fun x => by
    show L x ((c • ξ) x) = c • L x (ξ x)
    rw [lp.coeFn_smul, Pi.smul_apply, map_smul]

/-- The fibrewise action of a uniformly bounded family of operators. -/
def fibrewise (L : X → V →L[ℂ] V) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖L x‖ ≤ B) :
    Sections X V →L[ℂ] Sections X V :=
  (fibrewiseL L hB).mkContinuous B fun ξ =>
    lp.norm_le_of_forall_le (mul_nonneg hB0 (norm_nonneg ξ)) fun x => norm_fibrewise_le L hB ξ x

theorem fibrewise_apply (L : X → V →L[ℂ] V) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖L x‖ ≤ B)
    (ξ : Sections X V) (x : X) : fibrewise L hB0 hB ξ x = L x (ξ x) := rfl

/-- The product of a section with a bounded function. -/
def smulSec (h : X → ℂ) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (ξ : Sections X V) : Sections X V :=
  ⟨fun x => h x • ξ x, memℓp_infty ⟨B * ‖ξ‖, by
    rintro _ ⟨x, rfl⟩
    exact (norm_smul (h x) (ξ x)).trans_le (mul_le_mul (hB x)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero ξ x) (norm_nonneg _) ((norm_nonneg _).trans (hB x)))⟩⟩

theorem smulSec_apply (h : X → ℂ) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) (ξ : Sections X V) (x : X) :
    smulSec h hB ξ x = h x • ξ x := rfl

/-- An operator mapping `S` into the closed linear span of `S` preserves that closed span. -/
theorem mem_topologicalClosure_span_of_forall (L : Sections X V →L[ℂ] Sections X V)
    (S : Set (Sections X V)) (hS : ∀ ξ ∈ S, L ξ ∈ (Submodule.span ℂ S).topologicalClosure) :
    ∀ ξ ∈ (Submodule.span ℂ S).topologicalClosure,
      L ξ ∈ (Submodule.span ℂ S).topologicalClosure := by
  have hclosed : IsClosed (((Submodule.span ℂ S).topologicalClosure.comap
      (L : Sections X V →ₗ[ℂ] Sections X V) : Submodule ℂ (Sections X V)) : Set (Sections X V)) :=
    (Submodule.span ℂ S).isClosed_topologicalClosure.preimage L.continuous
  have hspan : Submodule.span ℂ S ≤ (Submodule.span ℂ S).topologicalClosure.comap
      (L : Sections X V →ₗ[ℂ] Sections X V) :=
    Submodule.span_le.2 hS
  exact fun ξ hξ => Submodule.topologicalClosure_minimal _ hspan hclosed hξ

/-- The restriction of an operator to an invariant submodule. -/
def restrictEnd (L : Sections X V →L[ℂ] Sections X V) (M : Submodule ℂ (Sections X V))
    (h : ∀ ξ ∈ M, L ξ ∈ M) : Module.End ℂ M :=
  (L : Sections X V →ₗ[ℂ] Sections X V).restrict h

theorem coe_restrictEnd_apply (L : Sections X V →L[ℂ] Sections X V)
    (M : Submodule ℂ (Sections X V)) (h : ∀ ξ ∈ M, L ξ ∈ M) (ξ : M) :
    ((restrictEnd L M h ξ : M) : Sections X V) = L ξ := rfl

end

end GroupApproximation.Toeplitz
