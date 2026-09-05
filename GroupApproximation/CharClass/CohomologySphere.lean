import GroupApproximation.CharClass.CohomologyBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyAboveDimension
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.SphereModTwoHomologyVanishing
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SphereTopCohomologyRankOne
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularH0General
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The mod-2 cohomology of a sphere, in the element-level vocabulary

`H^k(S^n; F₂)` is `F₂` in degrees `0` and `n` and vanishes otherwise.  The
vanishing statements and the top-degree rank computation are already in the
vendored tree (`SphereModTwoHomologyAboveDimension.lean`,
`SphereModTwoHomologyVanishing.lean`, `SphereTopCohomologyRankOne.lean`, all
routed through the mod-2 universal coefficient isomorphism
`kroneckerEquiv`); this file restates them over `Hmod2`, adds the degree-zero
computation for any nonempty path-connected space, and packages the top class as
an honest nonzero element with a linear equivalence `H^n(S^n; F₂) ≃ₗ F₂`.

`Sphere n` is the vendored model `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`,
so `Sphere 4` is the `S⁴` of `Analysis/LIXBlockProjections.lean`.

## Main declarations

* `sphere_coh_isZero_of_gt`, `sphere_coh_isZero_of_lt`, `sphere_coh_isZero_of_ne` —
  the vanishing range.
* `sphere_coh_top_finrank`, `sphereTopEquiv`, `sphereTopClass`,
  `sphereTopClass_ne_zero` — the top degree.
* `cohZeroEquiv` — `H^0(X; F₂) ≃ₗ F₂` for a nonempty path-connected `X`.
* `sphere_pathConnectedSpace` — `S^n` is path connected for `n ≥ 1`, so
  `cohZeroEquiv` applies to it.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AffineBarycentricSubdivision

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The vendored sphere cohomology is `Hmod2` of the vendored sphere -/

theorem sphereCohomology_eq (n k : ℕ) :
    sphereCohomology n k = Hmod2 (TopCat.of (Sphere n)) k := rfl

/-! ## 2. Vanishing -/

/-- `H^k(S^n; F₂) = 0` for `k > n`. -/
theorem sphere_coh_isZero_of_gt (n k : ℕ) (h : n < k) :
    Limits.IsZero (Hmod2 (TopCat.of (Sphere n)) k) :=
  sphereCohomology_isZero_of_gt n k h

/-- `H^k(S^n; F₂) = 0` for `0 < k < n`. -/
theorem sphere_coh_isZero_of_lt (n k : ℕ) (h0 : 0 < k) (hkn : k < n) :
    Limits.IsZero (Hmod2 (TopCat.of (Sphere n)) k) :=
  sphereCohomology_isZero_of_lt n k h0 hkn

/-- `H^k(S^n; F₂) = 0` whenever `k` is neither `0` nor `n`. -/
theorem sphere_coh_isZero_of_ne (n k : ℕ) (h0 : k ≠ 0) (hkn : k ≠ n) :
    Limits.IsZero (Hmod2 (TopCat.of (Sphere n)) k) := by
  rcases lt_or_gt_of_ne hkn with h | h
  · exact sphere_coh_isZero_of_lt n k (Nat.pos_of_ne_zero h0) h
  · exact sphere_coh_isZero_of_gt n k h

/-- Every class of `H^k(S^n; F₂)` vanishes when `k ∉ {0, n}`. -/
theorem sphere_coh_eq_zero_of_ne (n k : ℕ) (h0 : k ≠ 0) (hkn : k ≠ n)
    (a : Hmod2 (TopCat.of (Sphere n)) k) : a = 0 := by
  have h := sphere_coh_isZero_of_ne n k h0 hkn
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact h.elim a 0

/-! ## 3. The top degree -/

/-- `H^n(S^n; F₂)` is one dimensional (`n ≥ 1`). -/
theorem sphere_coh_top_finrank (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) (Hmod2 (TopCat.of (Sphere n)) n) = 1 :=
  sphere_top_cohomology_finrank_one_direct n hn

theorem sphere_coh_top_nontrivial (n : ℕ) (hn : 1 ≤ n) :
    Nontrivial (Hmod2 (TopCat.of (Sphere n)) n) :=
  Module.nontrivial_of_finrank_eq_succ (n := 0) (sphere_coh_top_finrank n hn)

theorem sphere_coh_top_finite (n : ℕ) (hn : 1 ≤ n) :
    Module.Finite (ZMod 2) (Hmod2 (TopCat.of (Sphere n)) n) :=
  Module.finite_of_finrank_pos (by rw [sphere_coh_top_finrank n hn]; exact Nat.one_pos)

/-- `H^n(S^n; F₂) ≃ₗ F₂` for `n ≥ 1`. -/
def sphereTopEquiv (n : ℕ) (hn : 1 ≤ n) :
    Hmod2 (TopCat.of (Sphere n)) n ≃ₗ[ZMod 2] ZMod 2 :=
  haveI := sphere_coh_top_finite n hn
  LinearEquiv.ofFinrankEq _ _ (by rw [sphere_coh_top_finrank n hn]; simp)

/-- A nonzero class in `H^n(S^n; F₂)`, `n ≥ 1`: the mod-2 fundamental class. -/
def sphereTopClass (n : ℕ) (hn : 1 ≤ n) : Hmod2 (TopCat.of (Sphere n)) n :=
  (sphereTopEquiv n hn).symm 1

theorem sphereTopClass_ne_zero (n : ℕ) (hn : 1 ≤ n) : sphereTopClass n hn ≠ 0 := by
  intro h
  have h1 : (1 : ZMod 2) = 0 := by
    have := congrArg (sphereTopEquiv n hn) h
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero h1

/-- Every class of `H^n(S^n; F₂)` is a multiple of the top class. -/
theorem sphere_coh_top_eq_smul (n : ℕ) (hn : 1 ≤ n) (a : Hmod2 (TopCat.of (Sphere n)) n) :
    a = (sphereTopEquiv n hn a) • sphereTopClass n hn := by
  rw [sphereTopClass, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-! ## 4. Degree zero -/

/-- `H^0(X; F₂) ≃ₗ F₂` for a nonempty path-connected space: the augmentation is
an isomorphism on `H₀`, and the universal coefficient isomorphism dualizes it. -/
def cohZeroEquiv (X : TopCat.{0}) [Nonempty X] [PathConnectedSpace X] :
    Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2 :=
  haveI : IsIso (H0aug (ZMod 2) X) := isIso_H0aug (R := ZMod 2) X
  ((kroneckerEquiv X 0).toLinearEquiv.trans
      (LinearEquiv.arrowCongr (asIso (H0aug (ZMod 2) X)).toLinearEquiv
        (LinearEquiv.refl (ZMod 2) (ZMod 2)))).trans
    (LinearMap.ringLmapEquivSelf (ZMod 2) (ZMod 2) (ZMod 2))

/-! ## 5. Path-connectedness of the sphere -/

theorem one_lt_rank_euclidean (n : ℕ) (hn : 1 ≤ n) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 :=
    finrank_euclideanSpace_fin
  have h2 : (1 : ℕ) < n + 1 := by omega
  rw [← Module.finrank_eq_rank, h]
  exact_mod_cast h2

theorem sphere_isPathConnected (n : ℕ) (hn : 1 ≤ n) :
    IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  isPathConnected_sphere (one_lt_rank_euclidean n hn) 0 zero_le_one

theorem sphere_pathConnectedSpace (n : ℕ) (hn : 1 ≤ n) : PathConnectedSpace (Sphere n) :=
  isPathConnected_iff_pathConnectedSpace.mp (sphere_isPathConnected n hn)

theorem sphere_nonempty (n : ℕ) (hn : 1 ≤ n) : Nonempty (Sphere n) := by
  obtain ⟨x, hx, -⟩ := sphere_isPathConnected n hn
  exact ⟨⟨x, hx⟩⟩

/-- `H^0(S^n; F₂) ≃ₗ F₂` for `n ≥ 1`. -/
def sphereCohZeroEquiv (n : ℕ) (hn : 1 ≤ n) :
    Hmod2 (TopCat.of (Sphere n)) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  haveI := sphere_nonempty n hn
  haveI := sphere_pathConnectedSpace n hn
  cohZeroEquiv (TopCat.of (Sphere n))

end

end GroupApproximation.CharClass
