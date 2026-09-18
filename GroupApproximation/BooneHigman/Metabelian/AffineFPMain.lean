import Mathlib.Data.Fintype.Card
import GroupApproximation.BooneHigman.Metabelian.AffineFPCompat
import GroupApproximation.BooneHigman.Metabelian.AffineFPPresentation

/-!
# The affine extension of a finitely presented elementary group (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp` (ESTABLISHED), proof
`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2.  For a finitely generated commutative
ring `R`, a finite index type `I` with at least four elements, and a finite set `S ∋ 1`
generating `R`, the presented group `PresAff I R S` is isomorphic to `R^I ⋊ E_I(R)`:

* `piMap`: `PresAff I R S →* R^I ⋊ E_I(R)` (the relators hold in the model);
* `psi`: the inverse, built with `SemidirectProduct.lift` from `zHom` and `compat`;
* `isFinitelyPresented_affine`: if `E_I(R)` is finitely presented, so is
  `R^I ⋊ E_I(R)`; `isFinitelyPresented_affine_fin` is the case `I = Fin n`, `n ≥ 4`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped commutatorElement

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

variable (I R) in
/-- The model map on the free product. -/
noncomputable def liftFree : FreeAff I R →* AffineElementary I R :=
  Monoid.Coprod.lift (SemidirectProduct.inr (φ := affAction I R))
    (FreeGroup.lift fun k : I =>
      (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k (1 : R) : I → R)) :
        AffineElementary I R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.liftFree

theorem liftFree_inl (g : elementaryGroup I R) :
    liftFree I R (Monoid.Coprod.inl g) = SemidirectProduct.inr g :=
  Monoid.Coprod.lift_apply_inl _ _ g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.liftFree_inl

theorem liftFree_inr_of (k : I) :
    liftFree I R (Monoid.Coprod.inr (FreeGroup.of k)) =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k (1 : R) : I → R)) :=
  by rw [liftFree, Monoid.Coprod.lift_apply_inr, FreeGroup.lift_apply_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.liftFree_inr_of

theorem rels_subset_ker (S : Set R) : rels I R S ⊆ (liftFree I R).ker := by
  rintro w ((⟨i, j, h, ε, -, k, hk, rfl⟩ | ⟨i, j, h, rfl⟩) | ⟨k, l, rfl⟩)
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, liftFree_inl,
      liftFree_inr_of]
    exact commutatorElement_eq_one_iff_commute.mpr (model_c1 i j h ε k hk)
  · rw [SetLike.mem_coe, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, liftFree_inl, liftFree_inr_of]
    exact mul_inv_eq_one.mpr (model_c2 i j h)
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, liftFree_inr_of,
      liftFree_inr_of]
    exact commutatorElement_eq_one_iff_commute.mpr (model_c3 k l)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.rels_subset_ker

/-- The map from the presented group to the model. -/
noncomputable def piMap (S : Set R) : PresAff I R S →* AffineElementary I R :=
  QuotientGroup.lift (relN I R S) (liftFree I R)
    (Subgroup.normalClosure_le_normal (rels_subset_ker S))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.piMap

theorem pi_mk (S : Set R) (w : FreeAff I R) :
    piMap S (QuotientGroup.mk' (relN I R S) w) = liftFree I R w :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.pi_mk

theorem pi_φP (S : Set R) (g : elementaryGroup I R) :
    piMap S (φP I R S g) = SemidirectProduct.inr g :=
  (pi_mk S (Monoid.Coprod.inl g)).trans (liftFree_inl g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.pi_φP

theorem pi_xP (S : Set R) (i j : I) (h : i ≠ j) (r : R) :
    piMap S (xP I R S i j h r) = SemidirectProduct.inr (elementaryRoot i j h r) :=
  pi_φP S (elementaryRoot i j h r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.pi_xP

theorem pi_τP (S : Set R) (k : I) :
    piMap S (τP I R S k) =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single k (1 : R) : I → R)) :=
  (pi_mk S (Monoid.Coprod.inr (FreeGroup.of k))).trans (liftFree_inr_of k)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.pi_τP

section Psi

variable {S : Set R} (h1 : (1 : R) ∈ S) (hcl : Subring.closure S = ⊤) (hI : 4 ≤ Fintype.card I)

/-- The map from the model to the presented group. -/
noncomputable def psi : AffineElementary I R →* PresAff I R S :=
  SemidirectProduct.lift (affineRel_presAff h1 hcl hI).zHom (φP I R S)
    ((affineRel_presAff h1 hcl hI).compat (φP I R S) fun _ _ _ _ => rfl)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.psi

theorem psi_inl (v : Multiplicative (I → R)) :
    psi h1 hcl hI (SemidirectProduct.inl v) = (affineRel_presAff h1 hcl hI).zHom v :=
  SemidirectProduct.lift_inl _ _ _ v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.psi_inl

theorem psi_inr (g : elementaryGroup I R) :
    psi h1 hcl hI (SemidirectProduct.inr g) = φP I R S g :=
  SemidirectProduct.lift_inr _ _ _ g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.psi_inr

theorem psi_comp_piMap : (psi h1 hcl hI).comp (piMap S) = MonoidHom.id (PresAff I R S) := by
  refine QuotientGroup.monoidHom_ext _ (Monoid.Coprod.hom_ext ?_ ?_)
  · refine MonoidHom.ext fun g => ?_
    exact (congrArg (psi h1 hcl hI) ((pi_mk S (Monoid.Coprod.inl g)).trans
      (liftFree_inl g))).trans (psi_inr h1 hcl hI g)
  · refine FreeGroup.ext_hom _ _ fun k => ?_
    exact (congrArg (psi h1 hcl hI) ((pi_mk S (Monoid.Coprod.inr (FreeGroup.of k))).trans
      (liftFree_inr_of k))).trans ((psi_inl h1 hcl hI _).trans
        (((affineRel_presAff h1 hcl hI).zHom_single k 1).trans
          ((affineRel_presAff h1 hcl hI).yi_one k)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.psi_comp_piMap

theorem piMap_comp_psi :
    (piMap S).comp (psi h1 hcl hI) = MonoidHom.id (AffineElementary I R) := by
  refine SemidirectProduct.hom_ext ?_ ?_
  · refine vec_hom_ext fun i r => ?_
    obtain ⟨k, hki, -, -⟩ := exists_ne_three hI i i i
    change piMap S (psi h1 hcl hI
        (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i r)))) =
      (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i r)) : AffineElementary I R)
    rw [psi_inl, AffineRel.zHom_single, AffineRel.yi_eq _ i k hki.symm r,
      map_commutatorElement, pi_xP, pi_τP]
    exact model_commutator i k hki.symm r
  · refine MonoidHom.ext fun g => ?_
    exact (congrArg (piMap S) (psi_inr h1 hcl hI g)).trans (pi_φP S g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.piMap_comp_psi

end Psi

/-- **Lane bh-met-05.** For a finitely generated commutative ring `R` and `|I| ≥ 4`, if the
elementary group `E_I(R)` is finitely presented then so is `R^I ⋊ E_I(R)`. -/
theorem isFinitelyPresented_affine [Algebra.FiniteType ℤ R]
    (hI : 4 ≤ Fintype.card I) [Group.IsFinitelyPresented (elementaryGroup I R)] :
    Group.IsFinitelyPresented (AffineElementary I R) := by
  obtain ⟨S, hS, h1, hcl⟩ := exists_finite_ring_generators R
  haveI := isFinitelyPresented_presAff (I := I) hS
  exact Group.IsFinitelyPresented.equiv (MonoidHom.toMulEquiv (piMap S) (psi h1 hcl hI)
    (psi_comp_piMap h1 hcl hI) (piMap_comp_psi h1 hcl hI))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.isFinitelyPresented_affine

/-- The case `I = Fin n`: `Group.IsFinitelyPresented (E_n R) → FP (R^n ⋊ E_n(R))`, `n ≥ 4`. -/
theorem isFinitelyPresented_affine_fin (n : ℕ) (hn : 4 ≤ n) (A : Type*) [CommRing A]
    [Algebra.FiniteType ℤ A] (hE : Group.IsFinitelyPresented (elementaryGroup (Fin n) A)) :
    Group.IsFinitelyPresented (AffineElementary (Fin n) A) :=
  isFinitelyPresented_affine (by rw [Fintype.card_fin]; exact hn)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.isFinitelyPresented_affine_fin

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
