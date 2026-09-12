import GroupApproximation.CharClass.LerayHirschInduction
import GroupApproximation.CharClass.CohomologyDeltaNatural
import GroupApproximation.CharClass.MayerVietorisZero
import GroupApproximation.CharClass.MayerVietorisSequence

/-!
# The ladder's inputs, instantiated on an honest cover

`LerayHirschSquares` states the ladder's hypotheses abstractly: `MVPulls` says
the four restrictions are pullbacks, `MVFacts` asks for δ-linearity over classes
from the ambient space and for exactness at the left end, and `MVLadder` asks for
a map of covered spaces with the connecting map natural.  Every one of those is
now a theorem of the concrete Mayer–Vietoris sequence, so this file discharges
them and the Mayer–Vietoris step of Leray–Hirsch stands on no hypotheses at all
beyond the bundle data.

The cover of the total space is the *preimage* of the cover of the base, which is
the only case a bundle argument ever needs, and `opensComap_sup_eq_top` says the
preimage of a cover is a cover.

## Main declarations

* `mvPulls` — the four restrictions of `mvSequence`, as pullbacks.
* `mvFacts` — δ-linearity (`MVDelta.mvDelta_cup`) and left-end exactness
  (`mvExactZero`).
* `mvLadderComap` — the map of covered spaces given by a map of spaces and the
  preimage cover; the four squares of spaces are `rfl` and the connecting map is
  natural by `MVDelta.mvDelta_naturality`.
* `bijective_lhSum_comap` — **the Mayer–Vietoris step, unconditional**.
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

/-- **The four Mayer–Vietoris restrictions, as pullbacks.** -/
def mvPulls (U V : Opens X) (hUV : U ⊔ V = ⊤) : MVPulls (mvSequence U V hUV) where
  iU := sInclusion ((U : Opens X) : Set X)
  iV := sInclusion ((V : Opens X) : Set X)
  jU := subInclusion (Set.inter_subset_left
    (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))
  jV := subInclusion (Set.inter_subset_right
    (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))
  resU_eq n x := by
    show (mvResU U V hUV n).hom x = _
    rw [mvResU_eq_pull]
    rfl
  resV_eq n x := by
    show (mvResV U V hUV n).hom x = _
    rw [mvResV_eq_pull]
    rfl
  resWU_eq n x := by
    show (mvResWU U V hUV n).hom x = _
    rw [mvResWU_eq_pull]
    rfl
  resWV_eq n x := by
    show (mvResWV U V hUV n).hom x = _
    rw [mvResWV_eq_pull]
    rfl

/-- The double restriction to the intersection is the pullback along the
inclusion of the intersection.  This is what puts `MVFacts.delta_cup` into the
spelling `MVDelta.mvDelta_cup` proves. -/
theorem resWU_resU_eq_pull (U V : Opens X) (hUV : U ⊔ V = ⊤) (q : ℕ) (b : Hmod2 X q) :
    (mvSequence U V hUV).resWU q ((mvSequence U V hUV).resU q b)
      = pull (sInclusion (((U : Opens X) : Set X) ∩ ((V : Opens X) : Set X))) q b := by
  rw [(mvPulls U V hUV).resWU_eq, (mvPulls U V hUV).resU_eq, ← pull_comp]
  exact pull_congr (subInclusion_comp_sInclusion (Set.inter_subset_left
    (s := ((U : Opens X) : Set X)) (t := ((V : Opens X) : Set X)))) q b

/-! ## 2. The two Mayer–Vietoris facts -/

/-- **The ladder's two Mayer–Vietoris facts, discharged.** -/
theorem mvFacts (U V : Opens X) (hUV : U ⊔ V = ⊤) : MVFacts (mvSequence U V hUV) where
  delta_cup p q a b := by
    rw [resWU_resU_eq_pull]
    exact MVDelta.mvDelta_cup U V hUV a b
  exactZero _ hU hV := mvExactZero U V hUV hU hV

/-! ## 3. The map of covered spaces -/

/-- **A map of spaces, with the preimage cover upstairs.**  The four squares of
spaces hold on the nose; the connecting map is natural by
`MVDelta.mvDelta_naturality`. -/
def mvLadderComap (f : P ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVLadder (mvPulls U V hUV)
      (mvPulls (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV)) where
  π := f
  πU := opensRestrict f U
  πV := opensRestrict f V
  πW := interRestrict f U V
  sqU := (opensRestrict_comp_sInclusion f U).symm
  sqV := (opensRestrict_comp_sInclusion f V).symm
  sqWU := (interRestrict_comp_subInclusionLeft f U V).symm
  sqWV := (interRestrict_comp_subInclusionRight f U V).symm
  delta_nat n a := MVDelta.mvDelta_naturality f U V hUV n a

/-! ## 4. The Mayer–Vietoris step, unconditional -/

/-- **The Mayer–Vietoris step of Leray–Hirsch, with no hypotheses left over.**
If `1, ξ, …, ξ^{r-1}` is a basis over each of the two preimages and over their
intersection, it is a basis over the whole total space. -/
theorem bijective_lhSum_comap (f : P ⟶ X) (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (ξ : Hmod2 P 2) (r : ℕ)
    (hU : ∀ n : ℕ, Function.Bijective
      (lhSum (opensRestrict f U)
        ((mvSequence (opensComap f U) (opensComap f V)
          (opensComap_sup_eq_top f hUV)).resU 2 ξ) r n))
    (hV : ∀ n : ℕ, Function.Bijective
      (lhSum (opensRestrict f V)
        ((mvSequence (opensComap f U) (opensComap f V)
          (opensComap_sup_eq_top f hUV)).resV 2 ξ) r n))
    (hW : ∀ n : ℕ, Function.Bijective
      (lhSum (interRestrict f U V)
        ((mvSequence (opensComap f U) (opensComap f V)
            (opensComap_sup_eq_top f hUV)).resWU 2
          ((mvSequence (opensComap f U) (opensComap f V)
            (opensComap_sup_eq_top f hUV)).resU 2 ξ)) r n))
    (n : ℕ) : Function.Bijective (lhSum f ξ r n) :=
  bijective_lhSum (mvPulls U V hUV)
    (mvPulls (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV))
    (mvLadderComap f U V hUV) (mvFacts U V hUV)
    (mvFacts (opensComap f U) (opensComap f V) (opensComap_sup_eq_top f hUV))
    ξ r hU hV hW n

end

end LH
end CharClass
end GroupApproximation
