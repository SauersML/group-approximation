import GroupApproximation.Higman.CentralHNNFreeLabelKernel
import GroupApproximation.Sofic.ProfiniteRetract

/-!
# Profinite closure for finite-base HNN subextensions

The finite-cover proof starts with the special free-factor feature exposed by
the free-label action: words supported on a selected set of labels form a
coordinate subgroup of a free group.  Killing every other basis letter is an
explicit retraction, so these coordinate subgroups are profinitely closed.

This is the terminal free-coordinate step in the finite-base HNN
subextension argument.  It is kept separate from any infinite-base lifting
criterion, which additionally has to supply cofinal quotients preserving the
relevant vertex products.
-/

namespace GroupApproximation
namespace Higman
namespace HNNSubextensionFiniteBaseProfinite

noncomputable section

namespace Coordinate

variable {ι : Type} (S : Set ι)

abbrev Sub : Subgroup (FreeGroup ι) :=
  Subgroup.closure (FreeGroup.of '' S)

/-- Killing the complementary basis letters always lands in the selected
coordinate subgroup. -/
theorem killOutside_mem (w : FreeGroup ι) :
    CentralHNNFreeLabel.Coordinate.killOutside S w ∈ Sub S := by
  classical
  induction w using FreeGroup.induction_on with
  | C1 => simp [Sub]
  | of i =>
      by_cases hi : i ∈ S
      · rw [CentralHNNFreeLabel.Coordinate.killOutside_of_mem hi]
        exact Subgroup.subset_closure ⟨i, hi, rfl⟩
      · rw [CentralHNNFreeLabel.Coordinate.killOutside_of_notMem hi]
        exact Subgroup.one_mem _
  | mul x y hx hy =>
      simpa only [map_mul] using (Sub S).mul_mem hx hy
  | inv_of i hi =>
      simpa only [map_inv] using (Sub S).inv_mem hi

/-- The coordinate projection with its codomain restricted to the selected
free factor. -/
def ret : FreeGroup ι →* Sub S :=
  (CentralHNNFreeLabel.Coordinate.killOutside S).codRestrict (Sub S)
    (killOutside_mem S)

theorem ret_comp_subtype :
    (ret S).comp (Sub S).subtype = MonoidHom.id (Sub S) := by
  apply MonoidHom.ext
  intro w
  apply Subtype.ext
  exact CentralHNNFreeLabel.Coordinate.killOutside_fixes w.property

/-- **Coordinate subgroups of a free group are profinitely closed.** -/
theorem profiniteClosure_sub : profiniteClosure (Sub S) = Sub S := by
  have h := profiniteClosure_range_eq_range_of_retraction
    (Sub S).subtype (ret S) (ret_comp_subtype S)
  simpa only [Subgroup.range_subtype] using h

end Coordinate

end

end HNNSubextensionFiniteBaseProfinite
end Higman
end GroupApproximation
