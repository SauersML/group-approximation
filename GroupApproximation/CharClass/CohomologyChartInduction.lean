import GroupApproximation.CharClass.CohomologyChartRankTwoInterface
import GroupApproximation.CharClass.ProjectiveSpaceStable

/-!
# The projective-factor Künneth at every rank, by induction on the fibre

`CohomologyChartSplit` runs the payoff chain over the product form `KnCP.CPSplit`
as a hypothesis.  This file discharges that hypothesis from the *fibre* statement
`KnCP.CPGenHyp` alone, by induction on `d`:

* the base `CPSplit 1` is `CohomologyChartRankTwoInterface`'s `lhSurj`, which is
  unconditional;
* the step `CPSplit d → CPSplit (d+1)` is Mayer–Vietoris for the chart cover of
  `U × ℂP^{d+1}`.

The step uses the inductive hypothesis twice.  Once to split the restriction to
the punctured piece, which is `U × ℂP^d`; once to *lift* the coefficient of the
generator back to the whole product, which is `mvResV_surjective_of_cpSplit` in
high degrees and `mvResV_surjective_of_lt` in low ones.  What is left over
restricts to zero on the punctured piece, so it is a multiple of `cpTop`, and
`CPGenHyp (d+1)` is exactly what turns that multiple into a multiple of the
generator.

Two inputs come from outside.  `cc-projective`'s `pull_cpIncl_cpGen` says the
hyperplane inclusion is essential on `H^2`, which is what makes the generator of
the fibre restrict to the generator of the smaller fibre; and
`cpTop_eq_pull_cpTopPt` says `cpTop` carries no base factor, which is what lets
`CPGenHyp` — a statement about `ℂP^{d+1}` with no base at all — reach it.

## Main declarations

* `KnCP.pull_punctIncl_cpGen`, `KnCP.pull_sInclusion_cpPrCP_cpGen` — the
  generator restricts to the generator, on the fibre and on the product.
* `KnCP.mvResV_surjective_of_cpSplit_all` — surjectivity in *every* degree.
* `KnCP.eq_zero_of_mvResV_eq_zero_of_lt` — injectivity below `2d+2`.
* `KnCP.exists_cup_gen_cpTop` — `cpTop` is the generator cupped with something.
* `KnCP.cpSplit_one`, `KnCP.cpSplit_succ`, `KnCP.cpSplit_of_cpGenHyp` — **the
  induction**.
* `KnCP.mvResV_surjective_of_cpGenHyp`, `KnCP.cpTop_cup_injective_of_cpGenHyp` —
  the two endpoints, with `CPGenHyp` the only hypothesis left.

The rank-two instantiation of `LH.bijective_lhSum_two` is not here: it is
`cc-projective`'s `LH.bijective_lhSum_cpProd`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The generator of the fibre restricts to the generator -/

/-- Pullback along `ℂP^d ⊆ ℂP^{d+1} ∖ {pt}` undoes pullback along the retraction. -/
theorem pull_cpInclP_pull_punctOpenHE (n : ℕ) (c : Hmod2 (CPtop d) n) :
    pull (cpInclP d) n (pull (cmap (punctOpenHomotopyEquiv d).toFun) n c) = c := by
  have h := (pullEquivOfHomotopyEquiv (punctOpenHomotopyEquiv d) n).symm_apply_apply c
  exact h

/-- **The generator of `ℂP^{d+1}` restricts to the generator of `ℂP^d`**, on the
punctured space rather than on the hyperplane.  This is `cc-projective`'s
`pull_cpIncl_cpGen` moved across the retraction. -/
theorem pull_punctIncl_cpGen (hd : 1 ≤ d) (hd1 : 1 ≤ d + 1) :
    pull (punctIncl d) 2 (cpGen (d + 1) hd1)
      = pull (cmap (punctOpenHomotopyEquiv d).toFun) 2 (cpGen d hd) := by
  refine (bijective_pull_cpInclP d 2).1 ?_
  rw [pull_cpInclP_pull_punctOpenHE, ← pull_comp]
  exact pull_cpIncl_cpGen d hd

/-- The punctured piece of the product, mapped to `cc-projective`'s punctured
space.  The membership proof is the one the point already carries, because the
product cover is the preimage of theirs. -/
def punctToPunctSpace : TopCat.of ↥(punctUSet U d) ⟶ punctSpace d :=
  cmap ⟨fun p => ⟨(p : U × CP (d + 1)).2, p.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

theorem punctToPunctSpace_comp_punctIncl :
    punctToPunctSpace U d ≫ punctIncl d
      = sInclusion (punctUSet U d) ≫ cpPrCP U d := by
  apply TopCat.Hom.ext
  ext p
  rfl

theorem punctToPunctSpace_comp_HE :
    punctToPunctSpace U d ≫ cmap (punctOpenHomotopyEquiv d).toFun
      = cmap (punctHomotopyEquiv U d).toFun ≫ cpSnd U d := by
  apply TopCat.Hom.ext
  ext p
  rfl

/-- **The generator, restricted to the punctured piece of the product**, is the
generator of the smaller product.  No comparison class and no change of basis. -/
theorem pull_sInclusion_cpPrCP_cpGen (hd : 1 ≤ d) (hd1 : 1 ≤ d + 1) :
    pull (sInclusion (punctUSet U d)) 2 (pull (cpPrCP U d) 2 (cpGen (d + 1) hd1))
      = pull (cmap (punctHomotopyEquiv U d).toFun) 2
          (pull (cpSnd U d) 2 (cpGen d hd)) := by
  have h1 : pull (sInclusion (punctUSet U d)) 2
        (pull (cpPrCP U d) 2 (cpGen (d + 1) hd1))
      = pull (punctToPunctSpace U d) 2
        (pull (punctIncl d) 2 (cpGen (d + 1) hd1)) := by
    rw [← pull_comp, ← pull_comp, punctToPunctSpace_comp_punctIncl]
  have h2 : pull (punctToPunctSpace U d) 2
        (pull (cmap (punctOpenHomotopyEquiv d).toFun) 2 (cpGen d hd))
      = pull (cmap (punctHomotopyEquiv U d).toFun) 2
          (pull (cpSnd U d) 2 (cpGen d hd)) := by
    rw [← pull_comp, ← pull_comp, punctToPunctSpace_comp_HE]
  rw [h1, pull_punctIncl_cpGen d hd hd1, h2]

/-! ## 2. Restriction to the punctured piece, in every degree -/

set_option maxHeartbeats 1000000 in
/-- **Surjectivity of the restriction in every degree**, over the product form.
Below the sphere dimension it is unconditional; above it, the product form
supplies the flatness that `mvResV_surjective_of_flat` wants. -/
theorem mvResV_surjective_of_cpSplit_all (hd : 1 ≤ d) (hsplit : CPSplit d) (k : ℕ)
    (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod2 (cpProdTop U d) k,
      (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w := by
  rcases Nat.lt_or_ge k (2 * d + 1) with hk | hk
  · exact mvResV_surjective_of_lt U d k hk w
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
    exact mvResV_surjective_of_cpSplit U d hd hsplit j w

set_option maxHeartbeats 1000000 in
/-- **Injectivity of the restriction below `2d+2`.**  A class killed by the
restriction is a connecting image, and the intersection is `U × S^{2d+1}`, which
below its dimension carries only pullbacks from `U`; those the connecting map
kills. -/
theorem eq_zero_of_mvResV_eq_zero_of_lt (k : ℕ) (hk : k < 2 * d + 2)
    (z : Hmod2 (cpProdTop U d) k)
    (h : (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = 0) : z = 0 := by
  have hU := mvResU_eq_zero_of_mvResV_eq_zero U d k z h
  match k with
  | 0 => exact mvExactZero (chartU U d) (punctU U d) (cp_sup U d) hU h
  | (j + 1) =>
    obtain ⟨w, hw⟩ := (mvExactX (chartU U d) (punctU U d) (cp_sup U d) j z).1 ⟨hU, h⟩
    obtain ⟨w', hw'⟩ :
        ∃ w', pull (cmap (interHomotopyEquiv U d).toFun) j w' = w :=
      ⟨(interPullEquiv U d j).symm w, (interPullEquiv U d j).apply_symm_apply w⟩
    obtain ⟨c, hcw⟩ := KnHemi.kunneth_low U (2 * d + 1) j (by omega) w'
    rw [← hw, ← hw', hcw, pull_interHE_prU, mvDelta_pull_cpPrSub_inter]

/-! ## 3. The top class is the generator cupped with something -/

set_option maxHeartbeats 1000000 in
/-- **`cpTop` is a multiple of the generator**, given generation on the fibre.
`cpTop` carries no base factor, so `CPGenHyp (d+1)` — a statement with no base in
it at all — applies to it verbatim. -/
theorem exists_cup_gen_cpTop (hgen : CPGenHyp (d + 1)) (hd1 : 1 ≤ d + 1) :
    ∃ γ : Hmod2 (cpProdTop U d) (2 * d),
      cpTop U d = cohCast (show 2 + 2 * d = 2 * d + 1 + 1 by omega)
        (cup (pull (cpPrCP U d) 2 (cpGen (d + 1) hd1)) γ) := by
  obtain ⟨c', hc'⟩ := hgen hd1 (2 * d)
    (cohCast (show 2 * d + 1 + 1 = 2 + 2 * d by omega) (cpTopPt d))
  refine ⟨pull (cpPrCP U d) (2 * d) c', ?_⟩
  have hpt : cpTopPt d = cohCast (show 2 + 2 * d = 2 * d + 1 + 1 by omega)
      (cup (cpGen (d + 1) hd1) c') := by
    rw [← hc', cohCast_cohCast, cohCast_self]
  rw [cpTop_eq_pull_cpTopPt, hpt, KnHemi.pull_cohCast, pull_cup]

/-! ## 4. The base of the induction -/

set_option maxHeartbeats 1000000 in
/-- **The product form at rank two**, unconditionally.  This is `lhSurj` with the
degree written the way `CPSplit` writes it and the two factors of the cup product
in the other order. -/
theorem cpSplit_one : CPSplit 1 := by
  intro V _inst _hd1 m z
  show ∃ (a : Hmod2 (TopCat.of V) (2 + m)) (y : Hmod2 (cpProdTop V 0) m),
      z = pull (cpPrU V 0) (2 + m) a + cup (cpTaut V) y
  obtain ⟨a, b, hab⟩ := lhSurj V m (cohCast (Nat.add_comm 2 m) z)
  refine ⟨cohCast (Nat.add_comm m 2) a, pull (cpPrU V 0) m b, ?_⟩
  have hz' := congrArg (cohCast (Nat.add_comm m 2)) hab
  rw [cohCast_cohCast, cohCast_self, cohCast_add, ← KnHemi.pull_cohCast] at hz'
  rw [hz', cup_comm (pull (cpPrU V 0) m b) (cpTaut V), cohCast_cohCast, cohCast_self]

/-! ## 5. The inductive step -/

set_option maxHeartbeats 1000000 in
/-- **The inductive step.**  Mayer–Vietoris for the chart cover of `U × ℂP^{d+1}`,
with the inductive hypothesis used both to split on the punctured piece and to
lift the coefficient back, and `CPGenHyp (d+1)` used once, on the residue. -/
theorem cpSplit_succ (hd : 1 ≤ d) (hgen : CPGenHyp (d + 1)) (hsplit : CPSplit d) :
    CPSplit (d + 1) := by
  intro V _inst hd1 m z
  show ∃ (a : Hmod2 (TopCat.of V) (2 + m)) (y : Hmod2 (cpProdTop V d) m),
      z = pull (cpPrU V d) (2 + m) a
        + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) y
  -- the restriction of `z` to the punctured piece, read on `V × ℂP^d`
  obtain ⟨w', hw'⟩ : ∃ w', pull (cmap (punctHomotopyEquiv V d).toFun) (2 + m) w'
      = (mvResV (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom z :=
    ⟨(punctPullEquiv V d (2 + m)).symm _, (punctPullEquiv V d (2 + m)).apply_symm_apply _⟩
  obtain ⟨a, y₀, hay⟩ := hsplit V hd m w'
  -- lift the coefficient of the generator to the whole product
  obtain ⟨Y, hY⟩ := mvResV_surjective_of_cpSplit_all V d hd hsplit m
    (pull (cmap (punctHomotopyEquiv V d).toFun) m y₀)
  have hYp : pull (sInclusion (punctUSet V d)) m Y
      = pull (cmap (punctHomotopyEquiv V d).toFun) m y₀ := by
    have h := hY
    rw [mvResV_eq_pull, cohPullback_apply_eq] at h
    exact h
  -- the model class agrees with `z` on the punctured piece
  have hres : (mvResV (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom
      (pull (cpPrU V d) (2 + m) a
        + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) Y)
      = (mvResV (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom z := by
    rw [map_add, mvResV_pull_cpPrU, ← hw', hay, pull_add, pull_punctHE_prU]
    congr 1
    rw [mvResV_eq_pull, cohPullback_apply_eq, pull_cup,
      pull_sInclusion_cpPrCP_cpGen V d hd hd1, hYp, ← pull_cup]
  have hzero : (mvResV (chartU V d) (punctU V d) (cp_sup V d) (2 + m)).hom
      (z + (pull (cpPrU V d) (2 + m) a
        + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) Y)) = 0 := by
    rw [map_add, hres, add_self_eq_zero_two]
  rcases Nat.lt_or_ge (2 + m) (2 * d + 2) with hlt | hge
  · -- below `2d+2` the restriction is injective, so the model class *is* `z`
    have hdiff := eq_zero_of_mvResV_eq_zero_of_lt V d (2 + m) hlt _ hzero
    refine ⟨a, Y, ?_⟩
    have hcg := congrArg (fun t => t + (pull (cpPrU V d) (2 + m) a
      + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) Y)) hdiff
    simpa only [add_assoc, add_self_eq_zero_two, add_zero, zero_add] using hcg
  · -- above it the difference is a multiple of `cpTop`, hence of the generator
    obtain ⟨j, hj⟩ : ∃ j, 2 + m = 2 * d + 1 + j + 1 := ⟨m - 2 * d, by omega⟩
    obtain ⟨b, hb⟩ :=
      exists_of_mvResV_eq_zero' V d (2 + m) j hj.symm (by omega) _ hzero
    obtain ⟨γ, hγ⟩ := exists_cup_gen_cpTop V d hgen hd1
    have hcup : cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1))
        (cohCast (show 2 * d + j = m by omega) (cup γ (pull (cpPrU V d) j b)))
        = cohCast (show 2 * d + 1 + 1 + j = 2 + m by omega)
            (cup (cpTop V d) (pull (cpPrU V d) j b)) := by
      rw [cup_cohCast_right, hγ, cup_cohCast_left, cup_assoc', cohCast_cohCast,
        cohCast_cohCast]
    refine ⟨a, Y + cohCast (show 2 * d + j = m by omega)
      (cup γ (pull (cpPrU V d) j b)), ?_⟩
    have h5 : z + (pull (cpPrU V d) (2 + m) a
        + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) Y)
        = cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1))
            (cohCast (show 2 * d + j = m by omega)
              (cup γ (pull (cpPrU V d) j b))) := hb.trans hcup.symm
    have h7 : z = cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1))
          (cohCast (show 2 * d + j = m by omega) (cup γ (pull (cpPrU V d) j b)))
        + (pull (cpPrU V d) (2 + m) a
          + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) Y) := by
      have hcg := congrArg (fun t => t + (pull (cpPrU V d) (2 + m) a
        + cup (pull (cpPrCP V d) 2 (cpGen (d + 1) hd1)) Y)) h5
      simpa only [add_assoc, add_self_eq_zero_two, add_zero] using hcg
    rw [h7, cup_add_right]
    abel

/-! ## 6. The induction -/

/-- **The projective-factor Künneth at every rank, from generation on the fibre.**
Nothing but `CPGenHyp` is consumed: no basis, no ring, no Gysin sequence.

The hypothesis is needed from rank two upwards only.  Rank one is the base case
and is unconditional, so a consumer never has to prove `CPGenHyp 1`. -/
theorem cpSplit_of_cpGenHyp (hgen : ∀ e : ℕ, 2 ≤ e → CPGenHyp e) :
    ∀ e : ℕ, 1 ≤ e → CPSplit e := by
  intro e
  induction e with
  | zero => exact fun h => absurd h (by omega)
  | succ n ih =>
    intro _hn
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact cpSplit_one
    · exact cpSplit_succ n (by omega) (hgen (n + 1) (by omega)) (ih (by omega))

/-! ## 7. The two endpoints, over generation on the fibre alone -/

/-- **The restriction to the punctured piece is surjective in every degree.** -/
theorem mvResV_surjective_of_cpGenHyp (hgen : ∀ e : ℕ, 2 ≤ e → CPGenHyp e)
    (hd : 1 ≤ d) (k : ℕ) (w : Hmod2 (TopCat.of ↥(punctUSet U d)) k) :
    ∃ z : Hmod2 (cpProdTop U d) k,
      (mvResV (chartU U d) (punctU U d) (cp_sup U d) k).hom z = w :=
  mvResV_surjective_of_cpSplit_all U d hd (cpSplit_of_cpGenHyp hgen d hd) k w

/-- **The `cpTop`-coefficient is unique at every rank.**  With the previous
theorem this says the restriction to the punctured piece is a split surjection
whose kernel is free of rank one on `cpTop`, over an arbitrary base. -/
theorem cpTop_cup_injective_of_cpGenHyp (hgen : ∀ e : ℕ, 2 ≤ e → CPGenHyp e)
    (hd : 1 ≤ d) (m : ℕ) (b : Hmod2 (TopCat.of U) m)
    (h : cup (cpTop U d) (pull (cpPrU U d) m b) = 0) : b = 0 :=
  cpTop_cup_injective U d hd (cpSplit_of_cpGenHyp hgen d hd) m b h

end KnCP

end

end GroupApproximation.CharClass
