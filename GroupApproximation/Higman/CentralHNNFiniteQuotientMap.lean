import GroupApproximation.Higman.HNNSubextensionFiniteBaseProfinite

/-!
# Central HNN maps induced by base quotients

A base homomorphism sends the centralized edge subgroup to its image and
therefore induces a homomorphism of central HNN extensions.  This is the map
used to reflect a finite normal-form obstruction to a finite-base HNN target.
-/

namespace GroupApproximation
namespace Higman
namespace CentralHNNFiniteQuotientMap

noncomputable section

variable {G Q : Type} [Group G] [Group Q]

private theorem commute_of_conj_eq {U : Type} [Group U] {u x : U}
    (h : u⁻¹ * x * u = x) : Commute u x := by
  show u * x = x * u
  calc
    u * x = u * (u⁻¹ * x * u) := by rw [h]
    _ = x * u := by group

/-- The central HNN homomorphism induced by a base homomorphism. -/
def map (M : Subgroup G) (q : G →* Q) :
    CentHNN M →* CentHNN (M.map q) := by
  refine HNNExtension.lift
    ((HNNExtension.of : Q →* CentHNN (M.map q)).comp q)
    HNNExtension.t ?_
  intro m
  have hm : q (m : G) ∈ M.map q := ⟨m, m.property, rfl⟩
  exact (commute_of_conj_eq (conj_eq_self_of_mem (M.map q) hm)).eq

@[simp] theorem map_of (M : Subgroup G) (q : G →* Q) (g : G) :
    map M q (HNNExtension.of g) = HNNExtension.of (q g) := by
  exact HNNExtension.lift_of _ _ _ _

@[simp] theorem map_t (M : Subgroup G) (q : G →* Q) :
    map M q (HNNExtension.t : CentHNN M) = HNNExtension.t := by
  exact HNNExtension.lift_t _ _ _

end

end CentralHNNFiniteQuotientMap
end Higman
end GroupApproximation
