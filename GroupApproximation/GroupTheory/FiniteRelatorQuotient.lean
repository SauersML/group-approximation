import GroupApproximation.GroupTheory.QuotientProtectedPair
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Literal finite-relator quotients

This is the constructive algebraic part of Hull's second quotient.  Starting
with an actual finite set of relators, it forms the quotient by their normal
closure and derives finite presentation, surjectivity, protection of a marked
pair, and saturation of a prescribed subgroup from a join equation upstairs.
No existence interface for small cancellation is introduced here.
-/

namespace GroupApproximation
namespace FiniteRelatorQuotient

universe u

variable {G : Type u} [Group G]

/-- The quotient obtained by adjoining the literal relators `R`. -/
abbrev Quotient (R : Set G) := G ⧸ Subgroup.normalClosure R

/-- Its canonical quotient map. -/
def quotientMap (R : Set G) : G →* Quotient R :=
  QuotientGroup.mk' (Subgroup.normalClosure R)

theorem quotientMap_surjective (R : Set G) :
    Function.Surjective (quotientMap R) :=
  QuotientGroup.mk'_surjective _

/-- Adjoining finitely many relators to a finitely presented group again gives
a finitely presented group. -/
theorem quotient_isFinitelyPresented [Group.IsFinitelyPresented G]
    {R : Set G} (hR : R.Finite) :
    Group.IsFinitelyPresented (Quotient R) :=
  Group.IsFinitelyPresented.quotient (Subgroup.normalClosure R)
    ⟨R, hR, rfl⟩

/-- Avoiding the relator normal closure is the concrete protected-pair
certificate for the finite-relator quotient. -/
theorem protectedPair_injective {R : Set G} {s : G}
    (hs : s ∉ Subgroup.normalClosure R) :
    Set.InjOn (quotientMap R) ({1, s} : Set G) :=
  QuotientProtectedPair.injOn_pair_of_not_mem _ hs

/-- The relator subgroup itself maps trivially to its quotient. -/
theorem normalClosure_map_eq_bot (R : Set G) :
    (Subgroup.normalClosure R).map (quotientMap R) = ⊥ := by
  ext q
  constructor
  · intro hq
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hq
    have hone : quotientMap R g = 1 :=
      (QuotientGroup.eq_one_iff g).mpr hg
    simpa only [Subgroup.mem_bot] using hone
  · intro hq
    simp only [Subgroup.mem_bot] at hq
    subst q
    exact Subgroup.one_mem _

/-- **Prescribed-subgroup saturation for a literal quotient.**

If the relator normal closure together with `D` generates the source group,
then the image of `D` is the whole quotient.  Thus the saturation field of the
Hull bridge can be checked before quotienting, by a concrete subgroup join
calculation. -/
theorem map_eq_top_of_normalClosure_sup_eq_top (R : Set G) (D : Subgroup G)
    (hjoin : Subgroup.normalClosure R ⊔ D = ⊤) :
    D.map (quotientMap R) = ⊤ := by
  have htop : (⊤ : Subgroup G).map (quotientMap R) = ⊤ := by
    exact Subgroup.map_top_of_surjective _ (quotientMap_surjective R)
  have hall : (Subgroup.normalClosure R ⊔ D).map (quotientMap R) = ⊤ := by
    rw [hjoin]
    exact htop
  rw [Subgroup.map_sup, normalClosure_map_eq_bot R] at hall
  simpa using hall

/-- Saturation after a source map: a prescribed subgroup of `E` maps onto the
finite-relator quotient whenever its image in `G`, together with the relator
normal closure, generates `G`. -/
theorem map_comp_eq_top_of_normalClosure_sup_map_eq_top
    {E : Type*} [Group E] (R : Set G) (D : Subgroup E) (f : E →* G)
    (hjoin : Subgroup.normalClosure R ⊔ D.map f = ⊤) :
    D.map ((quotientMap R).comp f) = ⊤ := by
  rw [← Subgroup.map_map]
  exact map_eq_top_of_normalClosure_sup_eq_top R (D.map f) hjoin

end FiniteRelatorQuotient
end GroupApproximation
