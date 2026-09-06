import GroupApproximation.CharClass.LerayHirschRel

/-!
# Leray–Hirsch over an open set of the base, and the two-set step

`LHOver f ξ r A` says the theorem holds over the part of the total space lying
over the open set `A`.  The Mayer–Vietoris step proved in `LerayHirschMV` says it
for a cover of the *whole* base, so to iterate it the ambient has to shrink, and
`LHOver_sup` is that step relativized: from `A`, `B` and `A ⊓ B` to `A ⊔ B`.

Everything is done inside `A ⊔ B`.  The two opens `A` and `B`, viewed there, do
cover, and `LerayHirschRel` identifies each of them with itself.  The only real
work is that the class on the total space, restricted twice, is the class
restricted once, which is `resWU_resU_eq_pull` on the total-space side.

## Main declarations

* `lhClass`, `LHOver` — the class and the statement, over an open set of the base.
* `LHOver_rel` — the theorem over `A` gives it over `A` viewed inside `C`.
* `LHOver_sup` — **the two-set step**.
* `topIso`, `LHOver_top` — over `⊤` the statement is the original one.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X P : TopCat.{0}}

/-! ## 1. The statement over an open set -/

/-- The Euler class, restricted to the part of the total space over `A`. -/
def lhClass (f : P ⟶ X) (ξ : Hmod2 P 2) (A : Opens X) :
    Hmod2 (opSpace (opensComap f A)) 2 :=
  pull (opIncl (opensComap f A)) 2 ξ

/-- **Leray–Hirsch over an open set of the base.** -/
def LHOver (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) (A : Opens X) : Prop :=
  ∀ n : ℕ, Function.Bijective (lhSum (opensRestrict f A) (lhClass f ξ A) r n)

/-! ## 2. Viewing the statement inside a larger open set -/

theorem opensComap_mono (f : P ⟶ X) {A C : Opens X} (h : A ≤ C) :
    opensComap f A ≤ opensComap f C := fun _ hp => h hp

/-- **The theorem over `A` gives the theorem over `A` viewed inside `C`.** -/
theorem LHOver_rel (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) (A C : Opens X) (h : A ≤ C)
    (hA : LHOver f ξ r A) (n : ℕ) :
    Function.Bijective
      (lhSum (opensRestrict (opensRestrict f C) (opRel A C))
        (pull (opIncl (opensComap (opensRestrict f C) (opRel A C))) 2 (lhClass f ξ C))
        r n) := by
  have h' : opensComap f A ≤ opensComap f C := opensComap_mono f h
  refine bijective_lhSum_of_iso _ (opensRestrict f A) (relIso A C h)
    (relIso (opensComap f A) (opensComap f C) h') (relIso_square f A C h h')
    _ (lhClass f ξ A) ?_ r n (hA n)
  unfold lhClass
  rw [← pull_comp, ← pull_comp, relIso_hom_comp_opIncl (opensComap f A) (opensComap f C) h']
  rfl

/-! ## 3. The two-set step -/

/-- **Leray–Hirsch for a union of two open sets.** -/
theorem LHOver_sup (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) (A B : Opens X)
    (hA : LHOver f ξ r A) (hB : LHOver f ξ r B) (hAB : LHOver f ξ r (A ⊓ B)) :
    LHOver f ξ r (A ⊔ B) := by
  intro n
  have hcov : opRel A (A ⊔ B) ⊔ opRel B (A ⊔ B) = ⊤ := opRel_sup_eq_top A B
  refine bijective_lhSum_comap (opensRestrict f (A ⊔ B)) (opRel A (A ⊔ B))
    (opRel B (A ⊔ B)) hcov (lhClass f ξ (A ⊔ B)) r ?_ ?_ ?_ n
  · intro m
    rw [(mvPulls (opensComap (opensRestrict f (A ⊔ B)) (opRel A (A ⊔ B)))
      (opensComap (opensRestrict f (A ⊔ B)) (opRel B (A ⊔ B)))
      (opensComap_sup_eq_top (opensRestrict f (A ⊔ B)) hcov)).resU_eq]
    exact LHOver_rel f ξ r A (A ⊔ B) le_sup_left hA m
  · intro m
    rw [(mvPulls (opensComap (opensRestrict f (A ⊔ B)) (opRel A (A ⊔ B)))
      (opensComap (opensRestrict f (A ⊔ B)) (opRel B (A ⊔ B)))
      (opensComap_sup_eq_top (opensRestrict f (A ⊔ B)) hcov)).resV_eq]
    exact LHOver_rel f ξ r B (A ⊔ B) le_sup_right hB m
  · intro m
    rw [resWU_resU_eq_pull]
    exact LHOver_rel f ξ r (A ⊓ B) (A ⊔ B) (le_trans inf_le_left le_sup_left) hAB m

/-! ## 4. Over the whole base -/

/-- The subspace cut out by `⊤` is the space. -/
def topIso (X : TopCat.{0}) : opSpace (⊤ : Opens X) ≅ X where
  hom := opIncl (⊤ : Opens X)
  inv := TopCat.ofHom ⟨fun x => ⟨x, trivial⟩, continuous_id.subtype_mk _⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Over `⊤` the relativized statement is the original one.** -/
theorem LHOver_top (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) (h : LHOver f ξ r ⊤) (n : ℕ) :
    Function.Bijective (lhSum f ξ r n) := by
  refine bijective_lhSum_of_iso f (opensRestrict f ⊤) (topIso X).symm (topIso P).symm
    rfl ξ (lhClass f ξ ⊤) ?_ r n (h n)
  show pull (topIso P).inv 2 (pull (topIso P).hom 2 ξ) = ξ
  rw [← pull_comp, (topIso P).inv_hom_id, pull_id]

end

end LH
end CharClass
end GroupApproximation
