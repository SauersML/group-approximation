import GroupApproximation.CharClass.LerayHirschTransport
import GroupApproximation.CharClass.CohomologyBridge

/-!
# Transporting Leray–Hirsch across a homotopy equivalence

`bijective_lhSum_of_iso` needs the comparison square to commute as a square of
spaces.  A trivialising open set of a base is compared with a point by a homotopy
equivalence, and such a square commutes only up to homotopy, so this file gives
the version that asks for the square in cohomology instead.

That hypothesis is strictly weaker and the original proof only ever used it: the
one place the square entered was a rewrite under `pull`.  Rule 11 keeps the
published statement as it is, so this is a second name rather than a weakening.

## Main declarations

* `bijective_colPull_of_bijective` — degreewise bijectivity passes to the column.
* `lhTerm_pull_of_coh`, `lhSum_pull_of_coh` — the naturality lemma over a square in
  cohomology.
* `bijective_lhSum_of_htpy` — **the transport**, over maps that are bijective on
  cohomology and a square that commutes there.
* `bijective_pull_of_homotopyEquiv` — the usual source of such maps.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X Y P Q : TopCat.{0}}

/-! ## 1. The column -/

/-- If a pullback is bijective in every degree, so is the induced map of columns.
The absent summands are filled with zero rather than with a chosen preimage, which
is what keeps the result inside the subgroup. -/
theorem bijective_colPull_of_bijective (f : Y ⟶ X) (r n : ℕ)
    (hb : ∀ m : ℕ, Function.Bijective (pull f m)) :
    Function.Bijective (colPull f r n) := by
  constructor
  · intro c c' h
    refine lhDomain_ext fun i => ?_
    refine (hb _).1 ?_
    have h' := lhDomain_apply_eq h i
    rwa [colPull_apply, colPull_apply] at h'
  · intro d
    obtain ⟨c, hc⟩ := lhDomain_choice
      (fun i x => pull f (n - 2 * (i : ℕ)) x
        = (d : (j : Fin r) → Hmod2 Y (n - 2 * (j : ℕ))) i)
      (fun i hi => by rw [pull_zero, lhDomain_vanish d i hi])
      (fun i _ => (hb _).2 _)
    exact ⟨c, lhDomain_ext fun i => by rw [colPull_apply]; exact hc i⟩

/-! ## 2. Naturality over a square in cohomology -/

theorem lhTerm_pull_of_coh (f : Y ⟶ X) (g : Q ⟶ P) (πP : P ⟶ X) (πQ : Q ⟶ Y)
    (hsq : ∀ (m : ℕ) (a : Hmod2 X m), pull g m (pull πP m a) = pull πQ m (pull f m a))
    (ξ : Hmod2 P 2) (n i : ℕ) (a : Hmod2 X (n - 2 * i)) :
    pull g n (lhTerm πP ξ n i a)
      = lhTerm πQ (pull g 2 ξ) n i (pull f (n - 2 * i) a) := by
  by_cases h : 2 * i ≤ n
  · rw [lhTerm_of_le πP ξ h, lhTerm_of_le πQ (pull g 2 ξ) h, pull_cohCast, pull_cup,
      hsq (n - 2 * i) a, pull_cupPowE]
  · rw [lhTerm_of_gt πP ξ h, lhTerm_of_gt πQ (pull g 2 ξ) h, pull_zero]

theorem lhSum_pull_of_coh (f : Y ⟶ X) (g : Q ⟶ P) (πP : P ⟶ X) (πQ : Q ⟶ Y)
    (hsq : ∀ (m : ℕ) (a : Hmod2 X m), pull g m (pull πP m a) = pull πQ m (pull f m a))
    (ξ : Hmod2 P 2) (r n : ℕ) (c : lhDomain X r n) :
    pull g n (lhSum πP ξ r n c)
      = lhSum πQ (pull g 2 ξ) r n (colPull f r n c) := by
  rw [lhSum_apply, lhSum_apply, pull_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [lhTerm_pull_of_coh f g πP πQ hsq, colPull_apply]

/-! ## 3. The transport -/

/-- **Leray–Hirsch transports across maps that are bijective on cohomology**, over a
square that commutes in cohomology.  A homotopy equivalence of situations is the
case this exists for. -/
theorem bijective_lhSum_of_htpy {X X' P P' : TopCat.{0}}
    (f : P ⟶ X) (f' : P' ⟶ X') (eX : X ⟶ X') (eP : P ⟶ P')
    (hbX : ∀ m : ℕ, Function.Bijective (pull eX m))
    (hbP : ∀ m : ℕ, Function.Bijective (pull eP m))
    (hsq : ∀ (m : ℕ) (a : Hmod2 X' m), pull eP m (pull f' m a) = pull f m (pull eX m a))
    (ξ : Hmod2 P 2) (ξ' : Hmod2 P' 2) (hξ : pull eP 2 ξ' = ξ) (r n : ℕ)
    (h : Function.Bijective (lhSum f' ξ' r n)) :
    Function.Bijective (lhSum f ξ r n) := by
  have key : ∀ c : lhDomain X' r n,
      pull eP n (lhSum f' ξ' r n c) = lhSum f ξ r n (colPull eX r n c) := by
    intro c
    rw [lhSum_pull_of_coh eX eP f' f hsq ξ' r n c, hξ]
  have hcomp : (fun c => lhSum f ξ r n c) ∘ (colPull eX r n)
      = (pull eP n) ∘ (fun c => lhSum f' ξ' r n c) :=
    funext fun c => (key c).symm
  have hb : Function.Bijective ((fun c => lhSum f ξ r n c) ∘ (colPull eX r n)) := by
    rw [hcomp]
    exact Function.Bijective.comp (hbP n) h
  exact bijective_of_comp_right _ _ hb (bijective_colPull_of_bijective eX r n hbX)

/-- A homotopy equivalence is bijective on cohomology in every degree. -/
theorem bijective_pull_of_homotopyEquiv {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : ContinuousMap.HomotopyEquiv A B) (n : ℕ) :
    Function.Bijective (pull (cmap e.toFun) n) :=
  (pullEquivOfHomotopyEquiv e n).bijective

end

end LH
end CharClass
end GroupApproximation
