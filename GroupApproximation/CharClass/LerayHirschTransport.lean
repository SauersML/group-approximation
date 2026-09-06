import GroupApproximation.CharClass.LerayHirschBridge

/-!
# Transporting Leray–Hirsch along an isomorphism of situations

The induction over a finite cover has to compare the theorem over an open set of
the base with the theorem over the *same* open set viewed inside a larger one.
Those two are not the same space on the nose, only canonically homeomorphic, so
the induction needs to move the statement across an isomorphism.  This file is
that move, and nothing else.

The proof is one application of `lhSum_pull`: an isomorphism of situations is in
particular a commuting square, so the Leray–Hirsch combination intertwines the
two, and both flanking maps are bijections.

## Main declarations

* `bijective_pull_iso`, `colPull_comp`, `colPull_id`, `bijective_colPull` — pullback
  along an isomorphism is bijective, on classes and on the column.
* `bijective_lhSum_of_iso` — **the transport**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

/-! ## 1. Pullback along an isomorphism -/

theorem bijective_pull_iso {X Y : TopCat.{0}} (e : X ≅ Y) (n : ℕ) :
    Function.Bijective (pull e.hom n) := by
  constructor
  · intro a b h
    have h' := congrArg (pull e.inv n) h
    rwa [← pull_comp, ← pull_comp, e.inv_hom_id, pull_id, pull_id] at h'
  · intro a
    exact ⟨pull e.inv n a, by rw [← pull_comp, e.hom_inv_id, pull_id]⟩

theorem colPull_comp {X Y Z : TopCat.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) (r n : ℕ)
    (c : lhDomain X r n) :
    colPull g r n (colPull f r n c) = colPull (g ≫ f) r n c :=
  lhDomain_ext fun i => by
    rw [colPull_apply, colPull_apply, colPull_apply, pull_comp]

theorem colPull_id {X : TopCat.{0}} (r n : ℕ) (c : lhDomain X r n) :
    colPull (𝟙 X) r n c = c :=
  lhDomain_ext fun i => by rw [colPull_apply, pull_id]

theorem bijective_colPull {X Y : TopCat.{0}} (e : X ≅ Y) (r n : ℕ) :
    Function.Bijective (colPull e.hom r n) := by
  constructor
  · intro c c' h
    have h' := congrArg (colPull e.inv r n) h
    rwa [colPull_comp, colPull_comp, e.inv_hom_id, colPull_id, colPull_id] at h'
  · intro c
    exact ⟨colPull e.inv r n c, by rw [colPull_comp, e.hom_inv_id, colPull_id]⟩

/-! ## 2. The transport -/

/-- **Leray–Hirsch transports along an isomorphism of situations.**  An isomorphism
of bases and an isomorphism of total spaces making the square commute and carrying
one class to the other move the theorem from one side to the other. -/
theorem bijective_lhSum_of_iso {X X' P P' : TopCat.{0}}
    (f : P ⟶ X) (f' : P' ⟶ X') (eX : X ≅ X') (eP : P ≅ P')
    (hsq : eP.hom ≫ f' = f ≫ eX.hom)
    (ξ : Hmod2 P 2) (ξ' : Hmod2 P' 2) (hξ : pull eP.hom 2 ξ' = ξ) (r n : ℕ)
    (h : Function.Bijective (lhSum f' ξ' r n)) :
    Function.Bijective (lhSum f ξ r n) := by
  have key : ∀ c : lhDomain X' r n,
      pull eP.hom n (lhSum f' ξ' r n c) = lhSum f ξ r n (colPull eX.hom r n c) := by
    intro c
    rw [lhSum_pull eX.hom eP.hom f' f hsq ξ' r n c, hξ]
  have hcomp : (fun c => lhSum f ξ r n c) ∘ (colPull eX.hom r n)
      = (pull eP.hom n) ∘ (fun c => lhSum f' ξ' r n c) :=
    funext fun c => (key c).symm
  have hb : Function.Bijective ((fun c => lhSum f ξ r n c) ∘ (colPull eX.hom r n)) := by
    rw [hcomp]
    exact Function.Bijective.comp (bijective_pull_iso eP n) h
  exact bijective_of_comp_right _ _ hb (bijective_colPull eX r n)

end

end LH
end CharClass
end GroupApproximation
