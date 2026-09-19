import GroupApproximation.CharClass.CohomologyChartRankTwo
import GroupApproximation.CharClass.ChernEulerBundle

/-!
# The projective-factor Künneth over the ring structure as a hypothesis

The general-rank step is blocked by a circle: flatness of the restriction to the
intersection *is* surjectivity, and surjectivity reduces to the projective Künneth
injectivity again.  What breaks it is the ring structure of `H^*(ℂP^d)`, which is
downstream of this file (`cc-projective` gets it from Gysin at rank two, over
`decomposition_zero`).  So the induction is run here over that structure as a
**named hypothesis**, and the instantiation is one line when it lands.

The induction consumes only **generation**, not a basis: every class of positive
even degree on the fibre is the degree-two generator cupped with a class two
degrees lower.  That is `KnCP.CPGenHyp`.

The payoff chain in this file is unconditional given the product form
`KnCP.CPSplit`: a class on the product is a pullback from the base plus the
generator cupped with something, the generator dies on the intersection by
`cc-projective`'s `eq_zero_interSpace_two`, so the class restricts to a pullback,
which is flatness, which is surjectivity.

## Main declarations

* `KnCP.CPGenHyp`, `KnCP.CPSplit` — the hypothesis and the product form.
* `KnCP.interToCP`, `KnCP.pull_interToPunct_snd_eq_zero` — the generator dies.
* `KnCP.flat_of_cpSplit`, `KnCP.mvResV_surjective_of_cpSplit`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-! ## 1. The hypothesis and the product form -/

/-- **The generation half of the ring structure, as a named hypothesis.**  Every
class of positive even degree on `ℂP^d` is the degree-two generator cupped with a
class two degrees lower.  A basis is strictly more than the induction uses. -/
def CPGenHyp (d : ℕ) : Prop :=
  ∀ (hd : 1 ≤ d) (k : ℕ) (c : Hmod2 (CPtop d) (2 + k)),
    ∃ c' : Hmod2 (CPtop d) k, c = cup (cpGen d hd) c'

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The two projections of `U × ℂP^d`. -/
abbrev cpFst : TopCat.of (U × CP d) ⟶ TopCat.of U := cmap ContinuousMap.fst
abbrev cpSnd : TopCat.of (U × CP d) ⟶ CPtop d := cmap ContinuousMap.snd

/-- **The product form of generation.**  Every class of degree `2 + m` on
`U × ℂP^d` is a pullback from `U` plus the generator cupped with a class of degree
`m`. -/
def CPSplit (d : ℕ) : Prop :=
  ∀ (U : Type) [TopologicalSpace U] (hd : 1 ≤ d) (m : ℕ)
    (z : Hmod2 (TopCat.of (U × CP d)) (2 + m)),
    ∃ (a : Hmod2 (TopCat.of U) (2 + m)) (y : Hmod2 (TopCat.of (U × CP d)) m),
      z = pull (cpFst U d) (2 + m) a
        + cup (pull (cpSnd U d) 2 (cpGen d hd)) y

/-! ## 2. The generator dies on the intersection -/

/-- The intersection, mapped into the projective space through the punctured piece. -/
def interToCP : interSpace d ⟶ CPtop d :=
  cmap ((punctOpenHomotopyEquiv d).toFun.comp
    ⟨fun p => ⟨(p : CP (d + 1)), p.2.2⟩,
      continuous_subtype_val.subtype_mk _⟩)

/-- The inclusion of the intersection into the punctured piece, in the product
model. -/
def interToPunctModel : TopCat.of ↥(interUSet U d) ⟶ TopCat.of (U × CP d) :=
  subInclusion (Set.inter_subset_right
      (s := (chartU U d : Set ↥(cpProdTop U d)))
      (t := (punctU U d : Set ↥(cpProdTop U d))))
    ≫ cmap (punctHomotopyEquiv U d).toFun

theorem interToPunctModel_comp_fst :
    interToPunctModel U d ≫ cpFst U d = cpPrSub U d (interUSet U d) := by
  rw [interToPunctModel, Category.assoc, punctHE_comp_prU, subInclusion_comp_cpPrSub]

theorem interToPunctModel_comp_snd :
    interToPunctModel U d ≫ cpSnd U d = interToInterSpace U d ≫ interToCP d := rfl

/-- **The generator restricted to the intersection vanishes**, because the
intersection has no cohomology in positive even degree. -/
theorem pull_interToPunct_snd_eq_zero (c : Hmod2 (CPtop d) 2) :
    pull (interToPunctModel U d) 2 (pull (cpSnd U d) 2 c) = 0 := by
  rw [← pull_comp, interToPunctModel_comp_snd, pull_comp,
    eq_zero_interSpace_two d (pull (interToCP d) 2 c), pull_zero]

/-! ## 3. Flatness, hence surjectivity -/

set_option maxHeartbeats 1000000 in
/-- **Flatness from the product form.** -/
theorem flat_of_cpSplit (hd : 1 ≤ d) (hsplit : CPSplit d) (k m : ℕ)
    (hk : 2 + m = k) (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) :
    ∃ e : Hmod2 (TopCat.of U) k,
      (mvResWV (chartU U d) (punctU U d) (cp_sup U d) k).hom w
        = pull (cpPrSub U d (interUSet U d)) k e := by
  subst hk
  obtain ⟨z, hz⟩ : ∃ z : Hmod2 (TopCat.of (U × CP d)) (2 + m),
      pull (cmap (punctHomotopyEquiv U d).toFun) (2 + m) z = w :=
    ⟨(punctPullEquiv U d (2 + m)).symm w,
      (punctPullEquiv U d (2 + m)).apply_symm_apply w⟩
  obtain ⟨a, y, hzay⟩ := hsplit U hd m z
  refine ⟨a, ?_⟩
  have hres : (mvResWV (chartU U d) (punctU U d) (cp_sup U d) (2 + m)).hom w
      = pull (interToPunctModel U d) (2 + m) z := by
    rw [mvResWV_eq_pull, cohPullback_apply_eq, ← hz, ← pull_comp, interToPunctModel]
  rw [hres, hzay, pull_add, ← pull_comp, interToPunctModel_comp_fst, pull_cup,
    pull_interToPunct_snd_eq_zero, zero_cup, add_zero]

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the restriction from the product form.** -/
theorem mvResV_surjective_of_cpSplit (hd : 1 ≤ d) (hsplit : CPSplit d) (m : ℕ)
    (w : Hmod2 (TopCat.of ↥(punctUSet U d)) (2 + m)) :
    ∃ z : Hmod2 (cpProdTop U d) (2 + m),
      (mvResV (chartU U d) (punctU U d) (cp_sup U d) (2 + m)).hom z = w := by
  obtain ⟨e, he⟩ := flat_of_cpSplit U d hd hsplit (2 + m) m rfl w
  exact mvResV_surjective_of_flat U d (2 + m) w e he

/-! ## 4. Uniqueness of the `cpTop`-coefficient -/

set_option maxHeartbeats 1000000 in
/-- **The `cpTop`-coefficient is unique.**  Over the hypothesis this is no longer
circular: `δ`-linearity turns the vanishing into a statement on the intersection,
exactness makes it a sum of restrictions, flatness makes both of those pullbacks
from the base, and the sphere Künneth's uniqueness finishes. -/
theorem cpTop_cup_injective (hd : 1 ≤ d) (hsplit : CPSplit d) (m : ℕ)
    (b : Hmod2 (TopCat.of U) m)
    (h : cup (cpTop U d) (pull (cpPrU U d) m b) = 0) : b = 0 := by
  have hb : (mvDelta (chartU U d) (punctU U d) (cp_sup U d) (2 * d + 1 + m)).hom
      (cup (interSigma U d) (pull (cpPrSub U d (interUSet U d)) m b)) = 0 := by
    have hc := MVDelta.mvDelta_cup (chartU U d) (punctU U d) (cp_sup U d)
      (interSigma U d) (pull (cpPrU U d) m b)
    rw [pull_sInclusion_cpPrU] at hc
    rw [hc, show (mvDelta (chartU U d) (punctU U d) (cp_sup U d)
      (2 * d + 1)).hom (interSigma U d) = cpTop U d from rfl, h, cohCast_zero]
  obtain ⟨a', b', hab⟩ :=
    (mvExactW (chartU U d) (punctU U d) (cp_sup U d) (2 * d + 1 + m) _).1 hb
  obtain ⟨e₁, he₁⟩ := exists_pull_cpPrSub_chart U d (2 * d + 1 + m) a'
  obtain ⟨e₂, he₂⟩ := flat_of_cpSplit U d hd hsplit (2 * d + 1 + m)
    (2 * d + m - 1) (by omega) b'
  have hflat : cup (interSigma U d) (pull (cpPrSub U d (interUSet U d)) m b)
      = pull (cpPrSub U d (interUSet U d)) (2 * d + 1 + m) (e₁ + e₂) := by
    rw [← hab, ← he₁, mvResWU_pull_cpPrSub, he₂, pull_add]
  -- move to the sphere model and use uniqueness there
  have hsphere : cup (knSigma U (2 * d + 1) (by omega))
        (pull (knPrY U (2 * d + 1)) m b)
      = pull (knPrY U (2 * d + 1)) (2 * d + 1 + m) (e₁ + e₂) := by
    refine (interPullEquiv U d (2 * d + 1 + m)).injective ?_
    show pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m) _
      = pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m) _
    rw [pull_cup, pull_interHE_prU, pull_interHE_prU]
    exact hflat
  refine KnHemi.kunneth_decomposition_unique U (2 * d + 1) (by omega)
    (2 * d + 1 + m) m rfl 0 (e₁ + e₂) b 0 ?_
  rw [pull_zero, zero_add, cohCast_self, cohCast_self, pull_zero, cup_zero, add_zero]
  exact hsphere

end KnCP

end

end GroupApproximation.CharClass
