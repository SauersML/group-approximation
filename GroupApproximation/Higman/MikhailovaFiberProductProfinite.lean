import GroupApproximation.Higman.MikhailovaFiberProduct
import GroupApproximation.Sofic.ProfiniteRetract

/-!
# Profinite closedness of the Mikhailova fibre product

The Mikhailova subgroup is the inverse image of the diagonal under the pair
of quotient maps.  Consequently it is profinitely closed whenever the
presented quotient is residually finite.  This is the positive-branch
separability fact needed to replace the corona-conjugator assumption by
finite HNN quotients.
-/

namespace GroupApproximation
namespace Higman
namespace Mikhailova

variable {G : Type*} [Group G]

/-- The two quotient coordinates at once. -/
def quotientPair (R : Set G) :
    G × G →* (G ⧸ Subgroup.normalClosure R) ×
      (G ⧸ Subgroup.normalClosure R) :=
  (quotientMap R).prodMap (quotientMap R)

@[simp] theorem quotientPair_apply (R : Set G) (a b : G) :
    quotientPair R (a, b) = (quotientMap R a, quotientMap R b) := rfl

/-- The fibre product is literally the inverse image of the diagonal. -/
theorem fiberProduct_eq_diagonal_comap (R : Set G) :
    fiberProduct R =
      (diagonalHom (G := G ⧸ Subgroup.normalClosure R)).range.comap
        (quotientPair R) := by
  ext p
  rcases p with ⟨a, b⟩
  constructor
  · intro hab
    rw [Subgroup.mem_comap]
    refine ⟨quotientMap R a, ?_⟩
    change
      (quotientMap R a, quotientMap R a) =
        (quotientMap R a, quotientMap R b)
    exact Prod.ext rfl hab
  · intro hp
    rw [Subgroup.mem_comap] at hp
    obtain ⟨q, hq⟩ := hp
    change
      (q, q) = (quotientMap R a, quotientMap R b) at hq
    exact (congrArg Prod.fst hq).symm.trans (congrArg Prod.snd hq)

/-- If the presented quotient is residually finite, its Mikhailova fibre
product is profinitely closed. -/
theorem profiniteClosure_fiberProduct
    (R : Set G) [Group.ResiduallyFinite (G ⧸ Subgroup.normalClosure R)] :
    profiniteClosure (fiberProduct R) = fiberProduct R := by
  rw [fiberProduct_eq_diagonal_comap]
  exact profiniteClosure_comap_eq_of_closed _ _
    profiniteClosure_diagonal_range

variable {X : Type*}

/-- Free-group form used by the finite-presentation compiler. -/
theorem profiniteClosure_freeSubgroup
    (R : Set (FreeGroup X))
    [Group.ResiduallyFinite
      (FreeGroup X ⧸ Subgroup.normalClosure R)] :
    profiniteClosure (freeSubgroup R) = freeSubgroup R := by
  rw [freeSubgroup_eq_fiberProduct]
  exact profiniteClosure_fiberProduct R

end Mikhailova
end Higman
end GroupApproximation
