import Mathlib.Tactic.Group
import GroupApproximation.BooneHigman.Metabelian.AffineFPConjugation
import GroupApproximation.BooneHigman.Metabelian.AffineFPModel

/-!
# Compatibility of `zHom` with the elementary action (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp-proof`, end of step F
(`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2).  Under `AffineRel S x τ`, and for a
homomorphism `φ : E_I(R) →* P` sending root elements to the `x`, the map `zHom : R^I →* P`
intertwines `affAction` with conjugation by `φ`:

* `conj_zHom`: `zHom (g • v) = φ g · zHom v · (φ g)⁻¹`, by induction on `g` in the closure of
  the root elements, using F4 (`conj_yi_ne`, `conj_yi_same`) on the generators;
* `compat`: the same statement in the form required by `SemidirectProduct.lift`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

namespace AffineRel

variable {I R P : Type*} [Fintype I] [DecidableEq I] [CommRing R] [Group P] {S : Set R}
  {x : ∀ i j : I, i ≠ j → R → P} {τ : I → P}

/-- `zHom` is equivariant for the action of a single root element. -/
theorem zHom_root (hR : AffineRel S x τ) (i j : I) (hij : i ≠ j) (a : R) :
    hR.zHom.comp (affAction I R (elementaryRoot i j hij a)).toMonoidHom =
      (MulAut.conj (x i j hij a)).toMonoidHom.comp hR.zHom := by
  refine vec_hom_ext fun l r => ?_
  change hR.zHom (affAction I R (elementaryRoot i j hij a)
      (Multiplicative.ofAdd (Pi.single l r))) =
    x i j hij a * hR.zHom (Multiplicative.ofAdd (Pi.single l r)) * (x i j hij a)⁻¹
  rw [affAction_root]
  by_cases hl : l = j
  · rw [hl, Pi.single_eq_same, ofAdd_add, map_mul hR.zHom, hR.zHom_single j r,
      hR.zHom_single i (a * r)]
    exact (hR.conj_yi_same i j hij a r).symm
  · rw [Pi.single_eq_of_ne (Ne.symm hl), mul_zero, Pi.single_zero, add_zero,
      hR.zHom_single l r]
    exact (hR.conj_yi_ne i j hij l (Ne.symm hl) a r).mul_inv_cancel.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.zHom_root

/-- `zHom` intertwines the elementary action with conjugation by `φ`. -/
theorem conj_zHom (hR : AffineRel S x τ) (φ : elementaryGroup I R →* P)
    (hφ : ∀ (i j : I) (h : i ≠ j) (r : R), φ (elementaryRoot i j h r) = x i j h r)
    (g : elementaryGroup I R) (v : Multiplicative (I → R)) :
    hR.zHom (affAction I R g v) = φ g * hR.zHom v * (φ g)⁻¹ := by
  have hg : g ∈ Subgroup.closure (elementaryRootSet I R) := by
    rw [elementaryRootSet_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    obtain ⟨i, j, hij, hg⟩ := hg
    obtain ⟨a, rfl⟩ := (mem_elementaryRootSubgroup_iff i j hij _).mp hg
    rw [hφ i j hij a]
    exact DFunLike.congr_fun (hR.zHom_root i j hij a) v
  | one =>
    simp only [map_one, MulAut.one_apply, one_mul, inv_one, mul_one]
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    rw [map_mul (affAction I R) g₁ g₂, MulAut.mul_apply, ih₁, ih₂, map_mul φ g₁ g₂]
    group
  | inv g _ ih =>
    have hw : affAction I R g (affAction I R g⁻¹ v) = v := by
      change (affAction I R g * affAction I R g⁻¹) v = v
      rw [← map_mul (affAction I R) g g⁻¹, mul_inv_cancel, map_one, MulAut.one_apply]
    have e := ih (affAction I R g⁻¹ v)
    rw [hw] at e
    rw [map_inv φ g, e]
    group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.conj_zHom

/-- The compatibility hypothesis of `SemidirectProduct.lift`. -/
theorem compat (hR : AffineRel S x τ) (φ : elementaryGroup I R →* P)
    (hφ : ∀ (i j : I) (h : i ≠ j) (r : R), φ (elementaryRoot i j h r) = x i j h r)
    (g : elementaryGroup I R) :
    hR.zHom.comp (affAction I R g).toMonoidHom =
      (MulAut.conj (φ g)).toMonoidHom.comp hR.zHom :=
  MonoidHom.ext fun v => hR.conj_zHom φ hφ g v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.compat

end AffineRel

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
