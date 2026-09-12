import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.LIXChernTopGamma
import GroupApproximation.CharClass.ThomCoordinates
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom class of the rank-`n` mapping-torus bundle pair, as a term, and its top coefficient

Lane `lix-oddside-n` (leaf (5)).

This is the rank-`n` counterpart of `CharClass/LIXThomClassOfTaut.lean`'s `lixTopCoeff`,
`CharClass/LIXThomClassTerm.lean`'s `lixLHplus`, `lixLHhyper`, `lixThomClassTerm`,
`CharClass/ThomCoordinates.lean`'s `thomJmTotal_lixThomClassTerm` and
`CharClass/LIXChernTopGamma.lean`'s `lixChern_top_eq_gamma`.  Every theorem the rank-two
versions apply (`hyperLH_range`, `thomJmTotal` and its injectivity and range,
`ThomDeg.thomEquiv`, `ThomDeg.jm_thomEquiv_symm`, `LH.component_chern_eq_gamma`,
`LH.gamma_of_iso`) is stated for an abstract `Bundle` over a compact Hausdorff base, so each
rank-`n` proof is the rank-two proof at `KGen.lixBundle n`.

The rank-two docstring's trap applies verbatim: every argument of the class is spelled exactly as
the theorem that discharges it spells it, in the term and in both theorems about it.

## Main declarations

* `KGen.lixTopCoeff n dd`, `lixTopCoeff_ne_zero`.
* `KGen.lixLHplus n`, `KGen.lixLHhyper n`.
* `KGen.lixThomClassTerm n hGc hGu`, `lixThomClassTerm_ne_zero`.
* `KGen.thomJmTotal_lixThomClassTerm` — the coordinates of the class.
* `KGen.lixChern_top_eq_gamma` — the top Chern class is the hyperplane presentation's `γ_r`.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

namespace KGen

noncomputable section

open ThomChernDeg LH

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The generator of the top coefficient group -/

/-- The generator of the top Leray–Hirsch coefficient group, which is `H^0` of the base. -/
def lixTopCoeff (n : ℕ) (dd : Fin ℓ → ℕ) :
    Hmod2 (lixN n dd) (2 * lixRank n dd - 2 * lixRank n dd) :=
  cohCast (by omega) (one (lixN n dd))

/-- **The generator is nonzero**, because the base is nonempty. -/
theorem lixTopCoeff_ne_zero (n : ℕ) (dd : Fin ℓ → ℕ) : lixTopCoeff n dd ≠ 0 := by
  haveI : Nonempty ↥(lixN n dd) := inferInstanceAs (Nonempty (↥sphereOne × Gen.baseM n dd))
  exact ThomChernDeg.cohCast_ne_zero _ (one_ne_zero_cohZero (lixN n dd))

/-! ## 2. Leray–Hirsch upstairs and downstairs -/

theorem rank_lixBundle_plusOne (n : ℕ)
    (G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (p : ↥sphereOne × Gen.baseM n dd) :
    (lixBundle n G hGc hGu).plusOne.rank p = lixRank n dd + 1 := by
  rw [Bundle.rank_plusOne, rank_lixBundle]

/-- Leray–Hirsch upstairs, at the projectivised sum. -/
theorem lixLHplus (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    LerayHirschGraded (projMapOf (lixBundle n G hGc hGu).plusOne)
      (tautEulerOf (lixBundle n G hGc hGu).plusOne) (lixRank n dd + 1) :=
  lerayHirschGraded_compact (lixBundle n G hGc hGu).plusOne (lixRank n dd + 1)
    (rank_lixBundle_plusOne n G hGc hGu) (Nat.succ_le_succ (Nat.zero_le _))

/-- Leray–Hirsch downstairs, on the hyperplane. -/
theorem lixLHhyper (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    LerayHirschGraded (hyperProj (lixBundle n G hGc hGu))
      (tautEulerRange (lixBundle n G hGc hGu)) (lixRank n dd) :=
  hyperLH_range (lixBundle n G hGc hGu) (lixRank n dd) (rank_lixBundle n G hGc hGu)
    (one_le_lixRank n dd)

/-! ## 3. The Thom class -/

/-- **The Thom class of the rank-`n` mapping-torus bundle pair, as a term.** -/
def lixThomClassTerm (n : ℕ) {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ↥(relCohomology (ZMod 2) (lixTotalPair n hGc hGu) (lixPuncturedInTotal n hGc hGu)
      (2 * lixRank n dd)) :=
  (ThomDeg.thomEquiv (M := fun i : Fin (lixRank n dd + 1) =>
      Hmod2 (TopCat.of (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd - 2 * (i : ℕ)))
    (fun i => chernMul (hyperLH_range (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd)) i)
    (thomJmTotal (lixBundle n G hGc hGu) (lixLHplus n hGc hGu))
    (injective_thomJmTotal (lixBundle n G hGc hGu) (one_le_lixRank n dd)
      (rank_lixBundle n G hGc hGu) (lixLHplus n hGc hGu))
    (range_thomJmTotal (lixBundle n G hGc hGu) (rank_lixBundle n G hGc hGu)
      (one_le_lixRank n dd) (lixLHplus n hGc hGu))).symm (lixTopCoeff n dd)

/-- **It is nonzero.** -/
theorem lixThomClassTerm_ne_zero (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixThomClassTerm n hGc hGu ≠ 0 :=
  thomClass_ne_zero (M := fun i : Fin (lixRank n dd + 1) =>
      Hmod2 (TopCat.of (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd - 2 * (i : ℕ)))
    (fun i => chernMul (hyperLH_range (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd)) i)
    (thomJmTotal (lixBundle n G hGc hGu) (lixLHplus n hGc hGu))
    (injective_thomJmTotal (lixBundle n G hGc hGu) (one_le_lixRank n dd)
      (rank_lixBundle n G hGc hGu) (lixLHplus n hGc hGu))
    (range_thomJmTotal (lixBundle n G hGc hGu) (rank_lixBundle n G hGc hGu)
      (one_le_lixRank n dd) (lixLHplus n hGc hGu))
    (lixTopCoeff_ne_zero n dd)

/-- **The coordinates of the rank-`n` Thom class**: the top one is the unit of the base, the rest
are the Chern coefficients of the hyperplane's presentation acting on it. -/
theorem thomJmTotal_lixThomClassTerm (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    thomJmTotal (lixBundle n G hGc hGu) (lixLHplus n hGc hGu) (lixThomClassTerm n hGc hGu)
      = ThomDeg.thomLift
          (fun i => chernMul (hyperLH_range (lixBundle n G hGc hGu) (lixRank n dd)
            (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd)) i)
          (lixTopCoeff n dd) :=
  ThomDeg.jm_thomEquiv_symm
    (M := fun i : Fin (lixRank n dd + 1) =>
      Hmod2 (TopCat.of (↥sphereOne × Gen.baseM n dd)) (2 * lixRank n dd - 2 * (i : ℕ)))
    (fun i => chernMul (hyperLH_range (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd)) i)
    (thomJmTotal (lixBundle n G hGc hGu) (lixLHplus n hGc hGu))
    (injective_thomJmTotal (lixBundle n G hGc hGu) (one_le_lixRank n dd)
      (rank_lixBundle n G hGc hGu) (lixLHplus n hGc hGu))
    (range_thomJmTotal (lixBundle n G hGc hGu) (rank_lixBundle n G hGc hGu)
      (one_le_lixRank n dd) (lixLHplus n hGc hGu))
    (lixTopCoeff n dd)

/-! ## 4. The top Chern class -/

/-- **The top Chern class of the mapping torus is the hyperplane presentation's `γ_r`.** -/
theorem lixChern_top_eq_gamma (n : ℕ)
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (hcont : Continuous (mappingTorus (Gen.Vmat n) G circHoriz circHeight))
    (hproj : ∀ p, IsStarProjection (mappingTorus (Gen.Vmat n) G circHoriz circHeight p)) :
    lixChern n dd (mappingTorus (Gen.Vmat n) G circHoriz circHeight) hcont hproj (lixRank n dd)
      = (lixLHhyper n hGc hGu).gamma (lixRank n dd) := by
  refine (lixChern_mappingTorus n G hGc hGu hcont hproj (lixRank n dd)).trans ?_
  refine (LH.component_chern_eq_gamma
    (lerayHirschGraded_compact (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd)) (lixRank n dd)).trans ?_
  exact LH.gamma_of_iso (hyperIso (lixBundle n G hGc hGu))
    (projMapOf (lixBundle n G hGc hGu)) (hyperProj (lixBundle n G hGc hGu))
    (hyperIso_hom_comp (lixBundle n G hGc hGu)) (tautEulerOf (lixBundle n G hGc hGu))
    (tautEulerRange (lixBundle n G hGc hGu)) rfl
    (lerayHirschGraded_compact (lixBundle n G hGc hGu) (lixRank n dd)
      (rank_lixBundle n G hGc hGu) (one_le_lixRank n dd)) (lixRank n dd)

end

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixTopCoeff_ne_zero
#audit_axioms KGen.lixThomClassTerm_ne_zero
#audit_axioms KGen.thomJmTotal_lixThomClassTerm
#audit_axioms KGen.lixChern_top_eq_gamma

end GroupApproximation.CharClass
