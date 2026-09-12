import GroupApproximation.CharClass.LerayHirschCover
import GroupApproximation.CharClass.CohomologyDeltaNaturalOf
import GroupApproximation.CharClass.MayerVietorisSequenceOf
import GroupApproximation.CharClass.MayerVietorisZeroOf

/-!
# The Mayer–Vietoris step of Leray–Hirsch over a field

The coefficient-generic form of `LerayHirschMV` and of the two-set step of `LerayHirschCover`.
The ladder of `LerayHirschInduction` is stated over any `K`; this file instantiates its
hypotheses on the Mayer–Vietoris sequence over a field `K` (`mvSequenceOf K`), so the
Mayer–Vietoris step of Leray–Hirsch stands on no hypotheses beyond the bundle data, over any
field.

* `mvPullsOf` — the four restrictions are pullbacks (`MayerVietorisPullOf`);
* `mvFactsOf` — δ-linearity (`MVDelta.mvDeltaOf_cup`) and left-end exactness
  (`mvExactZeroOf`);
* `mvLadderComapOf` — the map of covered spaces of a map of spaces and the preimage cover;
  the connecting square is `MVDelta.mvDeltaOf_naturality`.

A field is needed because the ambient identification of the Mayer–Vietoris sequence is.  The
`F₂` spellings `bijective_lhSum_comap` and `LerayHirschCover.LHOver_sup` are untouched.

## Main declarations

* `bijective_lhSum_comapOf` — **the Mayer–Vietoris step over a field, unconditional**.
* `LHOver_supOf` — the two-set step over a field.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X P : TopCat.{0}}

/-! ## 1. The restrictions are pullbacks -/

/-- **The four Mayer–Vietoris restrictions over a field, as pullbacks.** -/
def mvPullsOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVPulls (mvSequenceOf K U V hUV) where
  iU := sInclusion ((U : Opens X) : Set X)
  iV := sInclusion ((V : Opens X) : Set X)
  jU := subInclusion (Set.inter_subset_left
    (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))
  jV := subInclusion (Set.inter_subset_right
    (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))
  resU_eq n x := by
    show (mvResUOf K U V hUV n).hom x = _
    rw [mvResUOf_eq_pull]
    rfl
  resV_eq n x := by
    show (mvResVOf K U V hUV n).hom x = _
    rw [mvResVOf_eq_pull]
    rfl
  resWU_eq n x := by
    show (mvResWUOf K U V hUV n).hom x = _
    rw [mvResWUOf_eq_pull]
    rfl
  resWV_eq n x := by
    show (mvResWVOf K U V hUV n).hom x = _
    rw [mvResWVOf_eq_pull]
    rfl

/-- The double restriction to the intersection is the pullback along the inclusion of the
intersection. -/
theorem resWU_resU_eq_pullOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) (q : ℕ)
    (b : Hmod K X q) :
    (mvSequenceOf K U V hUV).resWU q ((mvSequenceOf K U V hUV).resU q b)
      = pull (sInclusion (((U : Opens X) : Set X) ∩ ((V : Opens X) : Set X))) q b := by
  rw [(mvPullsOf K U V hUV).resWU_eq, (mvPullsOf K U V hUV).resU_eq, ← pull_comp]
  exact pull_congr (subInclusion_comp_sInclusion (Set.inter_subset_left
    (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))) q b

/-! ## 2. The two Mayer–Vietoris facts -/

/-- **The ladder's two Mayer–Vietoris facts over a field, discharged.** -/
theorem mvFactsOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVFacts (mvSequenceOf K U V hUV) where
  delta_cup p q a b := by
    rw [resWU_resU_eq_pullOf]
    exact MVDelta.mvDeltaOf_cup K U V hUV a b
  exactZero _ hU hV := mvExactZeroOf K U V hUV hU hV

/-! ## 3. The map of covered spaces -/

/-- **A map of spaces, with the preimage cover upstairs**, over a field. -/
def mvLadderComapOf (K : Type) [Field K] (f : P ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVLadder (mvPullsOf K U V hUV)
      (mvPullsOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV)) where
  π := f
  πU := opensRestrict f U
  πV := opensRestrict f V
  πW := interRestrict f U V
  sqU := (opensRestrict_comp_sInclusion f U).symm
  sqV := (opensRestrict_comp_sInclusion f V).symm
  sqWU := (interRestrict_comp_subInclusionLeft f U V).symm
  sqWV := (interRestrict_comp_subInclusionRight f U V).symm
  delta_nat n a := MVDelta.mvDeltaOf_naturality K f U V hUV n a

/-! ## 4. The Mayer–Vietoris step over a field -/

/-- **The Mayer–Vietoris step of Leray–Hirsch over a field, with no hypotheses left over.**
If `1, ξ, …, ξ^{r-1}` is a basis over each of the two preimages and over their intersection,
it is a basis over the whole total space. -/
theorem bijective_lhSum_comapOf (K : Type) [Field K] (f : P ⟶ X) (U V : Opens X)
    (hUV : U ⊔ V = ⊤) (ξ : Hmod K P 2) (r : ℕ)
    (hU : ∀ n : ℕ, Function.Bijective
      (lhSum (opensRestrict f U)
        ((mvSequenceOf K (opensComap f U) (opensComap f V)
          (opensComap_sup_eq_top f hUV)).resU 2 ξ) r n))
    (hV : ∀ n : ℕ, Function.Bijective
      (lhSum (opensRestrict f V)
        ((mvSequenceOf K (opensComap f U) (opensComap f V)
          (opensComap_sup_eq_top f hUV)).resV 2 ξ) r n))
    (hW : ∀ n : ℕ, Function.Bijective
      (lhSum (interRestrict f U V)
        ((mvSequenceOf K (opensComap f U) (opensComap f V)
            (opensComap_sup_eq_top f hUV)).resWU 2
          ((mvSequenceOf K (opensComap f U) (opensComap f V)
            (opensComap_sup_eq_top f hUV)).resU 2 ξ)) r n))
    (n : ℕ) : Function.Bijective (lhSum f ξ r n) :=
  bijective_lhSum (mvPullsOf K U V hUV)
    (mvPullsOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV))
    (mvLadderComapOf K f U V hUV) (mvFactsOf K U V hUV)
    (mvFactsOf K (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV))
    ξ r hU hV hW n

/-! ## 5. The two-set step over a field -/

/-- **Leray–Hirsch for a union of two open sets, over a field.** -/
theorem LHOver_supOf (K : Type) [Field K] (f : P ⟶ X) (ξ : Hmod K P 2) (r : ℕ)
    (A B : Opens X) (hA : LHOver f ξ r A) (hB : LHOver f ξ r B)
    (hAB : LHOver f ξ r (A ⊓ B)) : LHOver f ξ r (A ⊔ B) := by
  intro n
  have hcov : opRel A (A ⊔ B) ⊔ opRel B (A ⊔ B) = ⊤ := opRel_sup_eq_top A B
  refine bijective_lhSum_comapOf K (opensRestrict f (A ⊔ B)) (opRel A (A ⊔ B))
    (opRel B (A ⊔ B)) hcov (lhClass f ξ (A ⊔ B)) r ?_ ?_ ?_ n
  · intro m
    rw [(mvPullsOf K (opensComap (opensRestrict f (A ⊔ B)) (opRel A (A ⊔ B)))
      (opensComap (opensRestrict f (A ⊔ B)) (opRel B (A ⊔ B)))
      (opensComap_sup_eq_top (opensRestrict f (A ⊔ B)) hcov)).resU_eq]
    exact LHOver_rel f ξ r A (A ⊔ B) le_sup_left hA m
  · intro m
    rw [(mvPullsOf K (opensComap (opensRestrict f (A ⊔ B)) (opRel A (A ⊔ B)))
      (opensComap (opensRestrict f (A ⊔ B)) (opRel B (A ⊔ B)))
      (opensComap_sup_eq_top (opensRestrict f (A ⊔ B)) hcov)).resV_eq]
    exact LHOver_rel f ξ r B (A ⊔ B) le_sup_right hB m
  · intro m
    rw [resWU_resU_eq_pullOf]
    exact LHOver_rel f ξ r (A ⊓ B) (A ⊔ B) (le_trans inf_le_left le_sup_left) hAB m

end

end LH
end CharClass
end GroupApproximation
