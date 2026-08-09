import NonsoficGroupsExist.Steinberg.Basic

/-!
# Functoriality of Steinberg presentations

A unital ring homomorphism acts coefficientwise on Steinberg generators.  The
three defining relations are functorial, so this action descends to the
presented Steinberg groups.  Surjective ring maps induce surjective group
maps.  This is the quotient-transport layer needed to descend the direct
free-algebra property-`(T)` theorem to finitely generated coefficient rings.
-/

namespace NonsoficGroupsExist
namespace SteinbergGroup

open scoped commutatorElement

variable {I R S : Type*} [Fintype I] [DecidableEq I] [Ring R] [Ring S]

/-- Apply a ring homomorphism to the coefficient of a Steinberg generator. -/
def mapGenerator (f : R →+* S) (g : SteinbergGenerator I R) :
    SteinbergGroup I S :=
  x g.row g.column g.row_ne_column (f g.coefficient)

private theorem mapGenerator_kills_relations (f : R →+* S)
    (w : FreeGroup (SteinbergGenerator I R))
    (hw : w ∈ relations (I := I) (R := R)) :
    FreeGroup.lift (mapGenerator f) w = 1 := by
  change IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, mapGenerator]
      change x i j hij (f a) * x i j hij (f b) *
        (x i j hij (f (a + b)))⁻¹ = 1
      rw [x_mul, map_add]
      simp
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, mapGenerator]
      change ⁅x i j hij (f a), x k l hkl (f b)⁆ = 1
      exact (x_commute_of_ne i j k l hij hkl hjk hli (f a) (f b)).commutator_eq
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement,
        FreeGroup.lift_apply_of, mapGenerator]
      change ⁅x i j hij (f a), x j k hjk (f b)⁆ *
        (x i k hik (f (a * b)))⁻¹ = 1
      rw [x_commutator, map_mul]
      simp
      all_goals assumption

/-- The coefficientwise homomorphism `St_I(R) → St_I(S)` induced by a
unital ring homomorphism `R → S`. -/
def ringMap (f : R →+* S) : SteinbergGroup I R →* SteinbergGroup I S :=
  PresentedGroup.toGroup (f := mapGenerator f)
    (mapGenerator_kills_relations f)

@[simp] theorem ringMap_x (f : R →+* S)
    (i j : I) (hij : i ≠ j) (a : R) :
    ringMap f (x i j hij a) = x i j hij (f a) := by
  exact PresentedGroup.toGroup.of _

/-- Surjectivity passes from a coefficient-ring map to its induced Steinberg
group map. -/
theorem ringMap_surjective_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) :
    Function.Surjective (ringMap (I := I) f) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  intro g _
  apply PresentedGroup.generated_by
    (relations (I := I) (R := S)) (ringMap f).range _ g
  rintro ⟨i, j, hij, b⟩
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨x i j hij a, ?_⟩
  change ringMap f (x i j hij a) = x i j hij (f a)
  exact ringMap_x f i j hij a

end SteinbergGroup
end NonsoficGroupsExist
