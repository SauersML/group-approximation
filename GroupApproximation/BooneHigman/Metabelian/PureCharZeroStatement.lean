import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Prod
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import GroupApproximation.BooneHigman.GroupRing.Generation
import GroupApproximation.BooneHigman.Metabelian.PureCharSplit
import GroupApproximation.BooneHigman.Metabelian.PureCharZeroSpan
import GroupApproximation.BooneHigman.Metabelian.PureCharZeroMatrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Char-zero linearity from a module statement (lane bh-met-19)

`PureCharLinearityZeroStatement` (`PureCharSplit`) is reduced to a strictly smaller statement
about modules only:

* `TorsionFreeModuleLinearityStatement`: let `Q` be a finitely generated abelian group and `W` a
  finitely generated `ℤ[Q]`-module that is torsion-free as an abelian group. Then some field `K`
  of characteristic zero has an injective additive map `ι : W →+ K^d` and a representation
  `ρ : Q →* GL_d(K)` with `ι (q • w) = ρ q · ι w`.

The reduction has no citation:
1. The Kaloujnine–Krasner cocycle `g ↦ (c_g, ḡ)` embeds `Γ` in `Affine ℤ Γᵃᵇ W`. Here `W` is
   finitely generated and torsion-free (`exists_affine_embedding`).
2. Adding the regular module `ℤ[Γᵃᵇ]` makes `ρ` faithful (`GroupRing.eq_one_of_smul_regular`).
3. The block matrices `[[ρ q, ι w], [0, 1]]` give a faithful representation (`kkAffGL_injective`).

Endpoint: `pureCharLinearityZero_of_torsionFreeModuleLinearity`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- A f.g. `ℤ[Q]`-module (`Q` f.g. abelian) that is torsion-free as an abelian group
embeds `Q`-equivariantly into `K^d` for a field `K` of characteristic zero. -/
def TorsionFreeModuleLinearityStatement : Prop :=
  ∀ (Q : Type) [CommGroup Q], Group.FG Q → ∀ (W : Type) [AddCommGroup W]
    [Module (MonoidAlgebra ℤ Q) W], Module.Finite (MonoidAlgebra ℤ Q) W → IsAddTorsionFree W →
    ∃ (K : Type) (_ : Field K) (d : ℕ) (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K)
      (ι : W →+ (Fin d → K)), ringChar K = 0 ∧ Function.Injective ι ∧
      ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
        Matrix.mulVec (ρ q : Matrix (Fin d) (Fin d) K) (ι w)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.TorsionFreeModuleLinearityStatement

theorem isAddTorsionFree_monoidAlgebra (Q : Type*) [CommGroup Q] :
    IsAddTorsionFree (MonoidAlgebra ℤ Q) :=
  Function.Injective.isAddTorsionFree
    (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Q)).toAddMonoidHom
    (MonoidAlgebra.coeffAddEquiv (R := ℤ) (M := Q)).injective

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isAddTorsionFree_monoidAlgebra

/-- **Reduction.** The module statement implies the char-zero linearity of f.g. metabelian groups
with torsion-free derived subgroup. -/
theorem pureCharLinearityZero_of_torsionFreeModuleLinearity
    (h : TorsionFreeModuleLinearityStatement) : PureCharLinearityZeroStatement := by
  intro Γ _ hfg hG htf
  obtain ⟨W, _, _, φ, _, _, hφ⟩ := exists_affine_embedding hfg hG htf
  haveI : Group.FG Γ := hfg
  haveI := isAddTorsionFree_monoidAlgebra (Abelianization Γ)
  obtain ⟨K, _, d, ρ, ι, hK, hι, hρι⟩ := h (Abelianization Γ)
    (GroupRing.group_fg_abelianization Γ) (W × MonoidAlgebra ℤ (Abelianization Γ))
    inferInstance inferInstance
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    refine GroupRing.eq_one_of_smul_regular (R := ℤ) (M := W) fun x => hι ?_
    rw [hρι, hq, Units.val_one, Matrix.one_mulVec]
  refine ⟨K, inferInstance, d + 1,
    (kkAffGL ρ ι hρι).comp ((GroupRing.affineAddRegular ℤ (Abelianization Γ) W).comp φ), hK, ?_⟩
  intro a b hab
  have h1 : GroupRing.affineAddRegular ℤ (Abelianization Γ) W (φ a) =
      GroupRing.affineAddRegular ℤ (Abelianization Γ) W (φ b) :=
    kkAffGL_injective ρ ι hρι hρ hι hab
  exact hφ (GroupRing.affineAddRegular_injective ℤ (Abelianization Γ) W h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.pureCharLinearityZero_of_torsionFreeModuleLinearity

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
