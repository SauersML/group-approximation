import GroupApproximation.Analysis.StateExtension
import GroupApproximation.Meta.AxiomGuard

/-!
# Positive extension of functionals from operator systems (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–56 (table row A2): the full C⋆-algebra of
a non-hyperlinear Kazhdan group cannot have the local lifting property (Ozawa, *About the QWEP
conjecture*, §7).  The proof goes through Arveson's extension theorem (Ozawa, Theorem 2.2), whose
first step is the Krein / M. Riesz extension of positive functionals.

This file proves that step for an **operator system**: a complex subspace `B` of a unital
C⋆-algebra that contains `1` and is closed under the star.  A linear functional on `B` that is
nonnegative on the positives of the ambient algebra extends to a functional on the whole algebra
with the same positivity (`exists_positive_extension_of_system`).

The rooted file `Analysis/StateExtension.lean` proves this for unital star subalgebras; its proof
uses only that the domain is a complex subspace containing the real scalars and closed under the
star.  The same argument runs here with the domain a `Submodule`.  The reassembly of a complex
functional from its real part (`StateExtension.complexify`) and the positive cone are reused.
This is a re-proof of the never-wired orphan `Analysis/OperatorSystemStateExtension.lean`
(left untouched).
-/

namespace GroupApproximation
namespace Full
namespace A2OperatorSystems

open scoped ComplexOrder
open StateExtension

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- A complex subspace containing `1` contains every real scalar. -/
theorem algebraMap_real_mem_of_one_mem (B : Submodule ℂ A) (h1 : (1 : A) ∈ B)
    (r : ℝ) : algebraMap ℝ A r ∈ B := by
  rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℂ r (1 : A)]
  exact B.smul_mem _ h1

section Domain

variable [PartialOrder A] [StarOrderedRing A]
variable (B : Submodule ℂ A)

/-- The self-adjoint elements of the operator system, as the domain of the real-linear extension
problem. -/
def systemSelfAdjointDomain : Submodule ℝ (selfAdjoint A) where
  carrier := {a | (a : A) ∈ B}
  add_mem' := fun {a b} ha hb => by
    show ((a + b : selfAdjoint A) : A) ∈ B
    show (a : A) + (b : A) ∈ B
    exact add_mem ha hb
  zero_mem' := by
    show ((0 : selfAdjoint A) : A) ∈ B
    show (0 : A) ∈ B
    exact zero_mem B
  smul_mem' := fun c a ha => by
    show ((c • a : selfAdjoint A) : A) ∈ B
    show (c : ℝ) • (a : A) ∈ B
    rw [← algebraMap_smul ℂ c (a : A)]
    exact B.smul_mem _ ha

variable (φ : B →ₗ[ℂ] ℂ)

/-- On self-adjoint elements of the operator system a positive functional takes real values:
shift by a real scalar to reduce to the positive case. -/
theorem system_phi_real_of_isSelfAdjoint (h1 : (1 : A) ∈ B)
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r)
    {b : B} (hb : IsSelfAdjoint (b : A)) :
    φ b = ((φ b).re : ℂ) := by
  set r : ℝ := ‖(b : A)‖ with hrdef
  have hu : (algebraMap ℝ A r) ∈ B := algebraMap_real_mem_of_one_mem B h1 r
  set u : B := ⟨algebraMap ℝ A r, hu⟩ with hudef
  have hcoe : ((b + u : B) : A) = (b : A) + algebraMap ℝ A r := rfl
  have hshift : 0 ≤ ((b + u : B) : A) := by
    rw [hcoe]
    have h1' : -(b : A) ≤ algebraMap ℝ A r := by
      have h := hb.neg.le_algebraMap_norm_self
      rwa [norm_neg] at h
    have h2 := add_le_add_right h1' (b : A)
    rw [add_neg_cancel] at h2
    exact h2
  have hupos : 0 ≤ ((u : B) : A) := algebraMap_real_nonneg (norm_nonneg _)
  obtain ⟨r₁, _, hr₁⟩ := hφ (b + u) hshift
  obtain ⟨r₂, _, hr₂⟩ := hφ u hupos
  have hb' : φ b = (r₁ : ℂ) - (r₂ : ℂ) := by
    rw [← hr₁, ← hr₂, ← map_sub, add_sub_cancel_right]
  rw [hb']
  norm_num

/-- The real-linear partial functional: real part of `φ` on the self-adjoint part of the
operator system. -/
def systemRealPartialFunctional : (selfAdjoint A) →ₗ.[ℝ] ℝ where
  domain := systemSelfAdjointDomain B
  toFun :=
    { toFun := fun a => (φ ⟨((a : selfAdjoint A) : A), a.property⟩).re
      map_add' := fun a b => by
        have h : (⟨(((a + b : systemSelfAdjointDomain B) : selfAdjoint A) : A),
            (a + b).property⟩ : B)
            = ⟨((a : selfAdjoint A) : A), a.property⟩
              + ⟨((b : selfAdjoint A) : A), b.property⟩ := by
          apply Subtype.ext
          rfl
        rw [h, map_add, Complex.add_re]
      map_smul' := fun c a => by
        have h : (⟨(((c • a : systemSelfAdjointDomain B) : selfAdjoint A) : A),
            (c • a).property⟩ : B)
            = (c : ℂ) • ⟨((a : selfAdjoint A) : A), a.property⟩ := by
          apply Subtype.ext
          show c • ((a : selfAdjoint A) : A)
              = (c : ℂ) • ((a : selfAdjoint A) : A)
          rw [← algebraMap_smul ℂ c ((a : selfAdjoint A) : A)]
          congr 1
        rw [h, map_smul]
        simp [smul_eq_mul, Complex.mul_re]
      }

/-- The M. Riesz extension: a real-linear functional on all self-adjoint elements, nonnegative on
positives, agreeing with `Re φ` on the operator system. -/
theorem system_exists_real_extension (h1 : (1 : A) ∈ B)
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ g : (selfAdjoint A) →ₗ[ℝ] ℝ,
      (∀ x : (systemRealPartialFunctional B φ).domain,
        g x = (systemRealPartialFunctional B φ) x) ∧
      ∀ x : selfAdjoint A, 0 ≤ (x : A) → 0 ≤ g x := by
  obtain ⟨g, hg1, hg2⟩ := riesz_extension positiveCone
    (systemRealPartialFunctional B φ)
    (fun x hx => by
      obtain ⟨r, hr0, hrφ⟩ := hφ
        ⟨((x : selfAdjoint A) : A), x.property⟩ hx
      show 0 ≤ (φ ⟨((x : selfAdjoint A) : A), x.property⟩).re
      rw [hrφ, Complex.ofReal_re]
      exact hr0)
    (fun y => by
      set r : ℝ := ‖(y : A)‖ with hrdef
      have hsa : IsSelfAdjoint (algebraMap ℝ A r) := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact IsSelfAdjoint.smul (star_trivial r) (star_one A)
      have hmem : ((⟨algebraMap ℝ A r, hsa⟩ : selfAdjoint A) : A) ∈ B := by
        show algebraMap ℝ A r ∈ B
        exact algebraMap_real_mem_of_one_mem B h1 r
      refine ⟨⟨⟨algebraMap ℝ A r, hsa⟩, hmem⟩, ?_⟩
      rw [mem_positiveCone]
      show 0 ≤ algebraMap ℝ A r + (y : A)
      have h1' : -((y : A)) ≤ algebraMap ℝ A r := by
        have h := (y.property).neg.le_algebraMap_norm_self
        rwa [norm_neg] at h
      have h2 := add_le_add_right h1' (y : A)
      rw [add_neg_cancel] at h2
      rwa [add_comm] at h2)
  exact ⟨g, hg1, fun x hx => hg2 x hx⟩

/-- The reassembled extension agrees with `φ` on the operator system. -/
theorem system_complexify_extends (h1 : (1 : A) ∈ B)
    (hstar : ∀ x ∈ B, star x ∈ B)
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r)
    (g : (selfAdjoint A) →ₗ[ℝ] ℝ)
    (hg : ∀ x : (systemRealPartialFunctional B φ).domain,
      g x = (systemRealPartialFunctional B φ) x)
    (b : B) : complexify g (b : A) = φ b := by
  have hre_mem : ((rePart (b : A) : selfAdjoint A) : A) ∈ B := by
    rw [rePart_coe, ← algebraMap_smul ℂ (2⁻¹ : ℝ) ((b : A) + star (b : A))]
    exact B.smul_mem _ (add_mem b.property (hstar _ b.property))
  have him_mem : ((imPart (b : A) : selfAdjoint A) : A) ∈ B := by
    rw [imPart_coe,
      ← algebraMap_smul ℂ (2⁻¹ : ℝ) ((-Complex.I) • ((b : A) - star (b : A)))]
    exact B.smul_mem _ (B.smul_mem _
      (sub_mem b.property (hstar _ b.property)))
  set bre : B := ⟨((rePart (b : A) : selfAdjoint A) : A), hre_mem⟩
  set bim : B := ⟨((imPart (b : A) : selfAdjoint A) : A), him_mem⟩
  have hgre : (g (rePart (b : A)) : ℂ) = φ bre := by
    have h := hg ⟨rePart (b : A), hre_mem⟩
    rw [h]
    exact (system_phi_real_of_isSelfAdjoint B φ h1 hφ
      (selfAdjoint.mem_iff.mp (rePart (b : A)).property)).symm
  have hgim : (g (imPart (b : A)) : ℂ) = φ bim := by
    have h := hg ⟨imPart (b : A), him_mem⟩
    rw [h]
    exact (system_phi_real_of_isSelfAdjoint B φ h1 hφ
      (selfAdjoint.mem_iff.mp (imPart (b : A)).property)).symm
  have hsum : bre + Complex.I • bim = b := by
    apply Subtype.ext
    show ((rePart (b : A) : selfAdjoint A) : A)
        + Complex.I • ((imPart (b : A) : selfAdjoint A) : A) = (b : A)
    exact rePart_add_I_smul_imPart (b : A)
  rw [complexify_apply, hgre, hgim, ← smul_eq_mul, ← map_smul, ← map_add,
    hsum]

end Domain

/-- **Positive extension from an operator system** (the Krein step of Ozawa, *About the QWEP
conjecture*, Theorem 2.2; table row A2, tex l.54–56).  A functional on a complex subspace that
contains `1` and is closed under the star, nonnegative on ambient positives, extends to the whole
algebra with the same positivity. -/
theorem exists_positive_extension_of_system [PartialOrder A] [StarOrderedRing A]
    {B : Submodule ℂ A} (h1 : (1 : A) ∈ B) (hstar : ∀ x ∈ B, star x ∈ B)
    {φ : B →ₗ[ℂ] ℂ}
    (hφ : ∀ b : B, 0 ≤ (b : A) → ∃ r : ℝ, 0 ≤ r ∧ φ b = r) :
    ∃ Φ : A →ₗ[ℂ] ℂ, (∀ b : B, Φ b = φ b) ∧
      ∀ a : A, 0 ≤ a → ∃ r : ℝ, 0 ≤ r ∧ Φ a = r := by
  obtain ⟨g, hg1, hg2⟩ := system_exists_real_extension B φ h1 hφ
  exact ⟨complexify g, system_complexify_extends B φ h1 hstar hφ g hg1,
    fun a ha => complexify_nonneg g hg2 ha⟩

end

end A2OperatorSystems
end Full
end GroupApproximation

open GroupApproximation.Full.A2OperatorSystems in
#audit_axioms exists_positive_extension_of_system
