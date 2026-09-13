import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Finite presentation passes to retracts

Fournier-Facio--Wu--Zaremsky Question 5.8 (arXiv:2603.24687v2) asks for a
type `[A_2]` action whose image is not finitely presented.  In the witness the
image is a semidirect product `Γ ⋊ Q` with `Q ≅ ℤ ≀ ℤ`.  The image is not
finitely presented because `Q` is not, and the step between the two is the
retraction `Γ ⋊ Q → Q`.

* `isFinitelyPresented_of_retract` -- a retract of a finitely presented group
  is finitely presented;
* `not_isFinitelyPresented_of_retract` -- the contrapositive;
* `not_isFinitelyPresented_semidirectProduct`, `not_isFinitelyPresented_prod`
  -- the contrapositive applied to the two standard retractions;
* `not_isFinitelyPresented_of_mulEquiv` -- invariance under isomorphism.

The proof of the first is the classical one.  Let `p : G → Q` be the
retraction and `i : Q → G` its section.  The kernel of `p` is the normal
closure of the finitely many corrections `x⁻¹ · i (p x)`, where `x` runs over
a finite generating set of `G`.  Modulo those corrections `i ∘ p` agrees with
the identity on the generators, hence everywhere, so an element killed by `p`
is trivial modulo them.  Mathlib's `Group.IsFinitelyPresented.of_surjective`
then presents `Q`.
-/

namespace GroupApproximation
namespace TypeA2

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- **A retract of a finitely presented group is finitely presented.** -/
theorem isFinitelyPresented_of_retract [hG : Group.IsFinitelyPresented G]
    (i : Q →* G) (p : G →* Q) (hpi : ∀ q, p (i q) = q) :
    Group.IsFinitelyPresented Q := by
  obtain ⟨n, φ, hφ, -⟩ := hG.out
  -- the finitely many round-trip corrections on the generators
  set S : Set G := Set.range fun j : Fin n =>
    (φ (FreeGroup.of j))⁻¹ * i (p (φ (FreeGroup.of j))) with hSdef
  refine Group.IsFinitelyPresented.of_surjective p (fun q => ⟨i q, hpi q⟩)
    ⟨S, Set.finite_range _, ?_⟩
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) ?_
  · rintro _ ⟨j, rfl⟩
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hpi, inv_mul_cancel]
  · intro x hx
    have hext : (QuotientGroup.mk' (Subgroup.normalClosure S)).comp φ =
        ((QuotientGroup.mk' (Subgroup.normalClosure S)).comp (i.comp p)).comp φ := by
      refine FreeGroup.ext_hom _ _ fun j => ?_
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq.mpr (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    obtain ⟨w, rfl⟩ := hφ x
    have hw := congrArg (fun f : FreeGroup (Fin n) →* G ⧸ Subgroup.normalClosure S => f w) hext
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hw
    rw [MonoidHom.mem_ker] at hx
    have hone : (φ w : G ⧸ Subgroup.normalClosure S) = 1 := by
      rw [hw, hx, map_one, QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff _).mp hone

/-- **Non-finite-presentability passes up from a retract.** -/
theorem not_isFinitelyPresented_of_retract (i : Q →* G) (p : G →* Q)
    (hpi : ∀ q, p (i q) = q) (hQ : ¬ Group.IsFinitelyPresented Q) :
    ¬ Group.IsFinitelyPresented G := fun hG =>
  hQ (isFinitelyPresented_of_retract (hG := hG) i p hpi)

/-- A semidirect product `N ⋊ Q` retracts onto `Q`, so it is not finitely
presented when `Q` is not. -/
theorem not_isFinitelyPresented_semidirectProduct {N : Type w} [Group N]
    {φ : Q →* MulAut N} (hQ : ¬ Group.IsFinitelyPresented Q) :
    ¬ Group.IsFinitelyPresented (N ⋊[φ] Q) :=
  not_isFinitelyPresented_of_retract SemidirectProduct.inr SemidirectProduct.rightHom
    SemidirectProduct.rightHom_inr hQ

/-- A direct product `N × Q` retracts onto `Q`, so it is not finitely presented
when `Q` is not. -/
theorem not_isFinitelyPresented_prod {N : Type w} [Group N]
    (hQ : ¬ Group.IsFinitelyPresented Q) : ¬ Group.IsFinitelyPresented (N × Q) :=
  not_isFinitelyPresented_of_retract (MonoidHom.inr N Q) (MonoidHom.snd N Q)
    (fun _ => rfl) hQ

/-- Non-finite-presentability is invariant under isomorphism. -/
theorem not_isFinitelyPresented_of_mulEquiv (e : G ≃* Q)
    (hG : ¬ Group.IsFinitelyPresented G) : ¬ Group.IsFinitelyPresented Q := fun hQ =>
  hG (Group.IsFinitelyPresented.equiv (h := hQ) e.symm)

end TypeA2
end GroupApproximation
