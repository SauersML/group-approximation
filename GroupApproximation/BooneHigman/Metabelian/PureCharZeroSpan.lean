import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.BooneHigman.Metabelian.PureCharZeroCocycle
import GroupApproximation.Meta.AxiomGuard

/-!
# A finitely generated torsion-free affine model (lane bh-met-19)

The cocycles `c_g` (`PureCharZeroCocycle`) span a `ℤ[Γᵃᵇ]`-submodule `kkSpan Γ` of the cocycle
space. By the cocycle identity, it is spanned by the cocycles of a generating set of `Γ`, so it
is a finitely generated module when `Γ` is a finitely generated group. The Kaloujnine–Krasner
homomorphism takes values in `Affine ℤ Γᵃᵇ (kkSpan Γ)`.

Endpoint: `exists_affine_embedding`. A finitely generated metabelian group with torsion-free
derived subgroup embeds in `Affine ℤ Γᵃᵇ W` for a finitely generated `ℤ[Γᵃᵇ]`-module `W` whose
additive group is torsion-free.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

section Span

variable {Γ : Type*} [Group Γ]

theorem kkCocycle_one : kkCocycle (1 : Γ) = 0 :=
  congrArg (fun z : GroupRing.Affine ℤ (Abelianization Γ) (KKSpace Γ) =>
    Multiplicative.toAdd z.left) (map_one (kkHom Γ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkCocycle_one

variable (Γ) in
/-- The `ℤ[Γᵃᵇ]`-submodule spanned by the cocycles. -/
def kkSpan : Submodule (MonoidAlgebra ℤ (Abelianization Γ)) (KKSpace Γ) :=
  Submodule.span _ (Set.range kkCocycle)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkSpan

/-- The cocycles of a generating set span all cocycles. -/
theorem kkCocycle_mem_span_image {T : Set Γ} (hT : Subgroup.closure T = ⊤) (g : Γ) :
    kkCocycle g ∈ Submodule.span (MonoidAlgebra ℤ (Abelianization Γ)) (kkCocycle '' T) := by
  let S := Submodule.span (MonoidAlgebra ℤ (Abelianization Γ)) (kkCocycle '' T)
  let H : Subgroup Γ :=
    { carrier := {a | kkCocycle a ∈ S}
      mul_mem' := fun {a b} ha hb => by
        show kkCocycle (a * b) ∈ S
        rw [kkCocycle_mul]
        exact S.add_mem ha (S.smul_mem _ hb)
      one_mem' := by
        show kkCocycle (1 : Γ) ∈ S
        rw [kkCocycle_one]
        exact S.zero_mem
      inv_mem' := fun {a} ha => by
        show kkCocycle a⁻¹ ∈ S
        have h : kkCocycle a⁻¹ +
            MonoidAlgebra.of ℤ (Abelianization Γ) (Abelianization.of a⁻¹) • kkCocycle a = 0 := by
          rw [← kkCocycle_mul, inv_mul_cancel, kkCocycle_one]
        rw [eq_neg_of_add_eq_zero_left h]
        exact S.neg_mem (S.smul_mem _ ha) }
  have hle : Subgroup.closure T ≤ H :=
    (Subgroup.closure_le H).mpr fun t ht => Submodule.subset_span (Set.mem_image_of_mem _ ht)
  have hg : g ∈ Subgroup.closure T := by
    rw [hT]
    exact Subgroup.mem_top g
  exact hle hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkCocycle_mem_span_image

theorem kkSpan_eq_span_image {T : Set Γ} (hT : Subgroup.closure T = ⊤) :
    kkSpan Γ = Submodule.span (MonoidAlgebra ℤ (Abelianization Γ)) (kkCocycle '' T) :=
  le_antisymm
    (Submodule.span_le.mpr (by
      rintro _ ⟨g, rfl⟩
      exact kkCocycle_mem_span_image hT g))
    (Submodule.span_mono (Set.image_subset_range _ _))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkSpan_eq_span_image

/-- The span of the cocycles of a finitely generated group is a finitely generated module. -/
theorem kkSpan_finite (hfg : Group.FG Γ) :
    Module.Finite (MonoidAlgebra ℤ (Abelianization Γ)) (kkSpan Γ) := by
  obtain ⟨T, hT, hTfin⟩ := Group.fg_iff.mp hfg
  exact Module.Finite.iff_fg.mpr (Submodule.fg_def.mpr
    ⟨kkCocycle '' T, hTfin.image _, (kkSpan_eq_span_image hT).symm⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkSpan_finite

theorem isAddTorsionFree_kkSpan (hG : IsMetabelianGroup Γ)
    (htf : ∀ x ∈ commutator Γ, ∀ n : ℕ, n ≠ 0 → x ^ n = 1 → x = 1) :
    IsAddTorsionFree (kkSpan Γ) :=
  haveI := isAddTorsionFree_kkSpace hG htf
  Function.Injective.isAddTorsionFree (kkSpan Γ).subtype.toAddMonoidHom Subtype.val_injective

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isAddTorsionFree_kkSpan

variable (Γ) in
/-- The Kaloujnine–Krasner homomorphism with values in the span of the cocycles. -/
noncomputable def kkSpanHom : Γ →* GroupRing.Affine ℤ (Abelianization Γ) (kkSpan Γ) :=
  MonoidHom.mk'
    (fun g => ⟨Multiplicative.ofAdd
      (⟨kkCocycle g, Submodule.subset_span (Set.mem_range_self g)⟩ : kkSpan Γ),
      Abelianization.of g⟩)
    fun g h => by
      refine SemidirectProduct.ext ?_ (map_mul Abelianization.of g h)
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      exact kkCocycle_mul g h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkSpanHom

theorem kkSpanHom_injective (hG : IsMetabelianGroup Γ) : Function.Injective (kkSpanHom Γ) := by
  intro g g' h
  have h2 : kkHom Γ g = kkHom Γ g' :=
    congrArg (GroupRing.affineMap (kkSpan Γ).subtype) h
  exact kkHom_injective hG h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.kkSpanHom_injective

end Span

/-- **Affine model.** A finitely generated metabelian group with torsion-free derived subgroup
embeds in `Affine ℤ Γᵃᵇ W` for a finitely generated torsion-free `ℤ[Γᵃᵇ]`-module `W`. -/
theorem exists_affine_embedding {Γ : Type} [Group Γ] (hfg : Group.FG Γ)
    (hG : IsMetabelianGroup Γ)
    (htf : ∀ x ∈ commutator Γ, ∀ n : ℕ, n ≠ 0 → x ^ n = 1 → x = 1) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (MonoidAlgebra ℤ (Abelianization Γ)) W)
      (φ : Γ →* GroupRing.Affine ℤ (Abelianization Γ) W),
      Module.Finite (MonoidAlgebra ℤ (Abelianization Γ)) W ∧ IsAddTorsionFree W ∧
        Function.Injective φ :=
  ⟨kkSpan Γ, inferInstance, inferInstance, kkSpanHom Γ, kkSpan_finite hfg,
    isAddTorsionFree_kkSpan hG htf, kkSpanHom_injective hG⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_affine_embedding

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
