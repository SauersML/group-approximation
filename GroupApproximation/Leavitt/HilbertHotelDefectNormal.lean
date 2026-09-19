import GroupApproximation.Leavitt.HilbertHotelBinary
import GroupApproximation.Steinberg.BinaryLeavitt

/-!
# The defect normally generates the model

The Hilbert-hotel defect is `e₁₃(q)` with `q = s₁r₁`, nonzero because
`r₁ q s₁ = 1` (`HilbertHotel.q_ne_zero`).  The Steinberg layer already proves
that *every* nonzero root element normally generates `St_n(R)` in rank `≥ 5`
(`BinaryLeavittSteinberg.normalClosure_root_eq_top`), so all that is needed to
put the defect in the same position inside the elementary group is to transport
normal generation along the canonical projection `St_n(R) ↠ EL_n(R)`.

**Direction matters, and only one direction is true.**  Normal generation pushes
*forward* along a surjection and does not pull back.  For `f : G ↠ M`,
`f (⟪S⟫) = ⟪f '' S⟫`, so `⟪S⟫ = G` gives `⟪f '' S⟫ = M`; but from `⟪s̄⟫ = M`
downstairs one recovers only `⟪s⟫ · ker f = G` upstairs, which is strictly weaker
whenever the kernel is nontrivial.  In particular a cover presentation does *not*
inherit `⟪d⟫ = ⊤` from its model — there the saturation has to be imposed as
relators, and what the model supplies is their consistency and the existence of
the words they name.  The lemmas below are therefore statements about the model
only, and `normalClosure_image_eq_top` is deliberately stated in the forward
direction so the false converse has no name to be quoted under.
-/

namespace GroupApproximation
namespace HilbertHotel

/-- **Normal generation pushes forward along a surjection.**  If `S` normally
generates `G` and `f : G →* M` is onto, then `f '' S` normally generates `M`.
The converse is false: see the module docstring. -/
theorem normalClosure_image_eq_top {G M : Type*} [Group G] [Group M]
    (f : G →* M) (hf : Function.Surjective f) (S : Set G)
    (hS : Subgroup.normalClosure S = ⊤) :
    Subgroup.normalClosure (f '' S) = ⊤ := by
  rw [← Subgroup.map_normalClosure S f hf, hS, Subgroup.map_top_of_surjective f hf]

/-- Every nonzero elementary root normally generates `EL_n(L_𝔽₂(1,2))` in rank at
least five: the Steinberg statement transported along the canonical projection. -/
theorem normalClosure_elementaryRoot_eq_top {n : ℕ} (hn : 5 ≤ n)
    (i j : Fin n) (hij : i ≠ j)
    {a : UniversalLeavitt.BinaryLeavittAlgebra} (ha : a ≠ 0) :
    Subgroup.normalClosure
        ({elementaryRoot i j hij a} : Set (BinaryLeavittSteinberg.ElementaryBase n)) = ⊤ := by
  have h := normalClosure_image_eq_top
    (SteinbergGroup.projection (I := Fin n) (R := UniversalLeavitt.BinaryLeavittAlgebra))
    (BinaryLeavittSteinberg.projection_surjective n)
    ({SteinbergGroup.x i j hij a})
    (BinaryLeavittSteinberg.normalClosure_root_eq_top hn i j hij ha)
  rwa [Set.image_singleton, SteinbergGroup.projection_x] at h

/-- **The defect normally generates the model.**  At the Hilbert-hotel frame
`N = 16`, the compression defect `e₁₃(q)` normally generates
`EL₁₆(L_𝔽₂(1,2))`.

This is a statement about the *model*.  A Shalom cover of it does not inherit the
conclusion; there the saturation relators are imposed, and this lemma is what
certifies their consistency. -/
theorem normalClosure_defect_eq_top (h02 : (0 : Fin 16) ≠ 2) :
    Subgroup.normalClosure
        ({elementaryRoot 0 2 h02 Binary.L.p1} :
          Set (BinaryLeavittSteinberg.ElementaryBase 16)) = ⊤ :=
  normalClosure_elementaryRoot_eq_top (by omega) 0 2 h02 Binary.q_ne_zero

end HilbertHotel
end GroupApproximation
