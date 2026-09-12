import GroupApproximation.CharClass.CohomologyChartRankTwoInterfaceOf

/-!
# The projective-factor Künneth over generation as a hypothesis, over a field

The coefficient-generic form of `CohomologyChartSplit`.  Over `F₂` the generation hypothesis and
the product form speak about the canonical generator `cpGen d hd`.  Over `K` there is no canonical
generator, so both are stated for **every nonzero** degree-two class: that is the form the rank
induction consumes, because the class at the smaller rank is the restriction of the class at the
larger one, which is nonzero but is not a chosen generator.

## Main declarations

* `KnCP.CPGenHypOf`, `KnCP.CPSplitOf` — the hypothesis and the product form over `K`.
* `KnCP.pull_interToPunct_snd_eq_zeroOf` — a class from the fibre dies on the intersection.
* `KnCP.flat_of_cpSplitOf`, `KnCP.mvResVOf_surjective_of_cpSplitOf`.
* `KnCP.cpTop_cup_injectiveOf` — **uniqueness of the `cpTopOf`-coefficient**, over the product form.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-! ## 1. The hypothesis and the product form -/

/-- **Generation on the fibre over `K`.**  Every class of positive even degree on `ℂP^e` is any
given nonzero degree-two class cupped with a class two degrees lower. -/
def CPGenHypOf (K : Type) [Field K] (e : ℕ) : Prop :=
  ∀ (h : Hmod K (CPtop e) 2), h ≠ 0 → ∀ (k : ℕ) (c : Hmod K (CPtop e) (2 + k)),
    ∃ c' : Hmod K (CPtop e) k, c = cup h c'

/-- **The product form over `K`.**  Every class of degree `2 + m` on `U × ℂP^e` is a pullback
from `U` plus the pullback of a given nonzero degree-two class cupped with a class of degree
`m`. -/
def CPSplitOf (K : Type) [Field K] (e : ℕ) : Prop :=
  ∀ (U : Type) [TopologicalSpace U] (h : Hmod K (CPtop e) 2), h ≠ 0 → ∀ (m : ℕ)
    (z : Hmod K (TopCat.of (U × CP e)) (2 + m)),
    ∃ (a : Hmod K (TopCat.of U) (2 + m)) (y : Hmod K (TopCat.of (U × CP e)) m),
      z = pull (cpFst U e) (2 + m) a + cup (pull (cpSnd U e) 2 h) y

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 2. A class from the fibre dies on the intersection -/

/-- **A degree-two class from the fibre, restricted to the intersection, vanishes**: the
intersection has no cohomology in positive even degree. -/
theorem pull_interToPunct_snd_eq_zeroOf (c : Hmod K (CPtop d) 2) :
    pull (interToPunctModel U d) 2 (pull (cpSnd U d) 2 c) = 0 := by
  have h2 : pull (interToCP d) 2 c = 0 :=
    CPn.eq_zero_interSpace_evenOf K d 1 one_ne_zero _
  rw [← pull_comp, interToPunctModel_comp_snd, pull_comp, h2, pull_zero]

/-! ## 3. Flatness, hence surjectivity -/

set_option maxHeartbeats 1000000 in
/-- **Flatness from the product form**, over `K`. -/
theorem flat_of_cpSplitOf (h : Hmod K (CPtop d) 2) (h0 : h ≠ 0) (hsplit : CPSplitOf K d)
    (k m : ℕ) (hk : 2 + m = k) (w : Hmod K (TopCat.of ↥(punctUSet U d)) k) :
    ∃ e : Hmod K (TopCat.of U) k,
      (mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) k).hom w
        = pull (cpPrSub U d (interUSet U d)) k e := by
  subst hk
  obtain ⟨z, hz⟩ : ∃ z : Hmod K (TopCat.of (U × CP d)) (2 + m),
      pull (cmap (punctHomotopyEquiv U d).toFun) (2 + m) z = w :=
    ⟨(punctPullEquivOf K U d (2 + m)).symm w,
      (punctPullEquivOf K U d (2 + m)).apply_symm_apply w⟩
  obtain ⟨a, y, hzay⟩ := hsplit U h h0 m z
  refine ⟨a, ?_⟩
  have hres : (mvResWVOf K (chartU U d) (punctU U d) (cp_sup U d) (2 + m)).hom w
      = pull (interToPunctModel U d) (2 + m) z := by
    rw [mvResWVOf_eq_pull, cohPullbackK_apply_eq, ← hz, ← pull_comp, interToPunctModel]
  rw [hres, hzay, pull_add, ← pull_comp, interToPunctModel_comp_fst, pull_cup,
    pull_interToPunct_snd_eq_zeroOf K U d h, zero_cup, add_zero]

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the restriction from the product form**, over `K`. -/
theorem mvResVOf_surjective_of_cpSplitOf (h : Hmod K (CPtop d) 2) (h0 : h ≠ 0)
    (hsplit : CPSplitOf K d) (m : ℕ) (w : Hmod K (TopCat.of ↥(punctUSet U d)) (2 + m)) :
    ∃ z : Hmod K (cpProdTop U d) (2 + m),
      (mvResVOf K (chartU U d) (punctU U d) (cp_sup U d) (2 + m)).hom z = w := by
  obtain ⟨e, he⟩ := flat_of_cpSplitOf K U d h h0 hsplit (2 + m) m rfl w
  exact mvResVOf_surjective_of_flat K U d (2 + m) w e he

/-! ## 4. Uniqueness of the `cpTopOf`-coefficient -/

set_option maxHeartbeats 1000000 in
/-- **The `cpTopOf`-coefficient is unique**, over the product form, over `K`. -/
theorem cpTop_cup_injectiveOf (hd : 1 ≤ d) (h : Hmod K (CPtop d) 2) (h0 : h ≠ 0)
    (hsplit : CPSplitOf K d) (m : ℕ) (b : Hmod K (TopCat.of U) m)
    (hcup : cup (cpTopOf K U d) (pull (cpPrU U d) m b) = 0) : b = 0 := by
  have hb : (mvDeltaOf K (chartU U d) (punctU U d) (cp_sup U d) (2 * d + 1 + m)).hom
      (cup (interSigmaOf K U d) (pull (cpPrSub U d (interUSet U d)) m b)) = 0 := by
    have hc := MVDelta.mvDeltaOf_cup K (chartU U d) (punctU U d) (cp_sup U d)
      (interSigmaOf K U d) (pull (cpPrU U d) m b)
    rw [pull_sInclusion_cpPrUOf] at hc
    rw [hc, show (mvDeltaOf K (chartU U d) (punctU U d) (cp_sup U d)
      (2 * d + 1)).hom (interSigmaOf K U d) = cpTopOf K U d from rfl, hcup, cohCast_zero]
  obtain ⟨a', b', hab⟩ :=
    (mvExactWOf K (chartU U d) (punctU U d) (cp_sup U d) (2 * d + 1 + m) _).1 hb
  obtain ⟨e₁, he₁⟩ := exists_pull_cpPrSub_chartOf K U d (2 * d + 1 + m) a'
  obtain ⟨e₂, he₂⟩ := flat_of_cpSplitOf K U d h h0 hsplit (2 * d + 1 + m)
    (2 * d + m - 1) (by omega) b'
  have hflat : cup (interSigmaOf K U d) (pull (cpPrSub U d (interUSet U d)) m b)
      = pull (cpPrSub U d (interUSet U d)) (2 * d + 1 + m) (e₁ + e₂) := by
    rw [← hab, ← he₁, mvResWUOf_pull_cpPrSub, he₂, pull_add]
  have hsphere : cup (knSigmaOf K U (2 * d + 1) (by omega))
        (pull (knPrY U (2 * d + 1)) m b)
      = pull (knPrY U (2 * d + 1)) (2 * d + 1 + m) (e₁ + e₂) := by
    refine (interPullEquivOf K U d (2 * d + 1 + m)).injective ?_
    show pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m) _
      = pull (cmap (interHomotopyEquiv U d).toFun) (2 * d + 1 + m) _
    rw [pull_cup, pull_interHE_prUOf, pull_interHE_prUOf]
    exact hflat
  refine KnHemi.kunneth_decomposition_uniqueOf K U (2 * d + 1) (by omega)
    (2 * d + 1 + m) m rfl 0 (e₁ + e₂) b 0 ?_
  rw [pull_zero, zero_add, cohCast_self, cohCast_self, pull_zero, cup_zero, add_zero]
  exact hsphere

end KnCP

end

end GroupApproximation.CharClass
