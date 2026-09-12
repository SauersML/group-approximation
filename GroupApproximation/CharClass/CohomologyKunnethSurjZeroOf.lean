import GroupApproximation.CharClass.CohomologyKunnethSurjOf
import GroupApproximation.CharClass.CohomologyKunnethZeroOf
import GroupApproximation.CharClass.CohomologyKunnethSurjZero
import GroupApproximation.CharClass.MayerVietorisDisjointOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The base of the Künneth decomposition over a field: the zero sphere

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethSurjZero` with coefficients in a field `K`.  `Y × S⁰` is
covered by two disjoint opens, `KnZero.zPos` and `KnZero.zNeg` of the `F₂` file (coefficient-free),
each homotopy equivalent to `Y` through the projection, so a class is determined by its two
restrictions (`mvResPairOf_eq_zero_of_disjoint`, lane `lix-lh`).  The generator `zeroGenOf K`
restricts to `1` on the positive piece and to `0` on the negative one.

**What changes over `K`.**  If `z` restricts to `pr^* a_U` and `pr^* a_V`, the `F₂` file takes
`a = a_V` and `b = a_U + a_V`.  Over `K` the second coefficient is the **difference**
`b = a_U − a_V`: on the positive piece `pr^* a_V + 1 ⌣ pr^* (a_U − a_V) = pr^* a_U`, on the negative
one `pr^* a_V + 0`.

## Main declarations

* `KnZero.exists_pull_zPrSub_posOf`, `KnZero.exists_pull_zPrSub_negOf`.
* `KnZero.mvResUOf_pull_knPrY`, `KnZero.mvResVOf_pull_knPrY`,
  `KnZero.pull_sInclusion_zeroGen_posOf`, `KnZero.pull_sInclusion_zeroGen_negOf`.
* `KnZero.knTop_zeroOf` — the base case over `K`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnZero

/-! ## 1. Each piece is `Y`, over `K` -/

theorem exists_pull_zPrSub_posOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (a : Hmod K (TopCat.of ↥(zPosSet Y)) m) :
    ∃ c : Hmod K (TopCat.of Y) m, pull (zPrSub Y (zPosSet Y)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquivOf K (zPosHomotopyEquiv Y) m).symm a, ?_⟩
  rw [zPrSub_pos_eq]
  exact (pullEquivOfHomotopyEquivOf K (zPosHomotopyEquiv Y) m).apply_symm_apply a

theorem exists_pull_zPrSub_negOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (m : ℕ)
    (a : Hmod K (TopCat.of ↥(zNegSet Y)) m) :
    ∃ c : Hmod K (TopCat.of Y) m, pull (zPrSub Y (zNegSet Y)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquivOf K (zNegHomotopyEquiv Y) m).symm a, ?_⟩
  rw [zPrSub_neg_eq]
  exact (pullEquivOfHomotopyEquivOf K (zNegHomotopyEquiv Y) m).apply_symm_apply a

/-! ## 2. The two restrictions -/

theorem mvResUOf_pull_knPrY (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (a : Hmod K (TopCat.of Y) k) :
    (mvResUOf K (zPos Y) (zNeg Y) (z_sup Y) k).hom (pull (knPrY Y 0) k a)
      = pull (zPrSub Y (zPosSet Y)) k a := by
  rw [mvResUOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, sInclusion_comp_zPrSub]

theorem mvResVOf_pull_knPrY (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (k : ℕ)
    (a : Hmod K (TopCat.of Y) k) :
    (mvResVOf K (zPos Y) (zNeg Y) (z_sup Y) k).hom (pull (knPrY Y 0) k a)
      = pull (zPrSub Y (zNegSet Y)) k a := by
  rw [mvResVOf_eq_pull, cohPullbackK_apply_eq, ← pull_comp, sInclusion_comp_zPrSub]

theorem pull_sInclusion_zeroGen_posOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] :
    pull (sInclusion (zPosSet Y)) 0 (pull (knPrS Y 0) 0 (KnHemi.zeroGenOf K))
      = one (TopCat.of ↥(zPosSet Y)) := by
  have hres : pull (sInclusion (KnHemi.szPos : Set ↥(TopCat.of (Sphere 0)))) 0
      (KnHemi.zeroGenOf K) = one (mvU KnHemi.szPos) := by
    rw [← cohPullbackK_apply_eq, ← mvResUOf_eq_pull K KnHemi.szPos KnHemi.szNeg KnHemi.sz_sup 0]
    exact KnHemi.mvResUOf_zeroGenOf K
  rw [← pull_comp, ← zPosToPos_comp, pull_comp, hres, pull_one]

theorem pull_sInclusion_zeroGen_negOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] :
    pull (sInclusion (zNegSet Y)) 0 (pull (knPrS Y 0) 0 (KnHemi.zeroGenOf K)) = 0 := by
  have hres : pull (sInclusion (KnHemi.szNeg : Set ↥(TopCat.of (Sphere 0)))) 0
      (KnHemi.zeroGenOf K) = 0 := by
    rw [← cohPullbackK_apply_eq, ← mvResVOf_eq_pull K KnHemi.szPos KnHemi.szNeg KnHemi.sz_sup 0]
    exact KnHemi.mvResVOf_zeroGenOf K
  rw [← pull_comp, ← zNegToNeg_comp, pull_comp, hres, pull_zero]

theorem pull_sInclusion_knPrY_posOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    (S : Set ↥(zProdTop Y)) (k : ℕ) (a : Hmod K (TopCat.of Y) k) :
    pull (sInclusion S) k (pull (knPrY Y 0) k a) = pull (zPrSub Y S) k a := by
  rw [← pull_comp, sInclusion_comp_zPrSub]

/-! ## 3. The base case -/

set_option maxHeartbeats 1000000 in
/-- **The base of the Künneth decomposition over `K`.** -/
theorem knTop_zeroOf (K : Type) [Field K] : KnHemi.KnTopOf K 0 (KnHemi.zeroGenOf K) := by
  intro Y _ k m hk z
  obtain rfl : k = 0 + m := hk.symm
  obtain ⟨aU, haU⟩ := exists_pull_zPrSub_posOf K Y (0 + m)
    ((mvResUOf K (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom z)
  obtain ⟨aV, haV⟩ := exists_pull_zPrSub_negOf K Y (0 + m)
    ((mvResVOf K (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom z)
  refine ⟨aV, cohCast (Nat.zero_add m) (aU - aV), ?_⟩
  have hpc : ∀ {p p' : ℕ} (h : p = p') (x : Hmod K (TopCat.of Y) p),
      pull (zPrSub Y (zPosSet Y)) p' (cohCast h x)
        = cohCast h (pull (zPrSub Y (zPosSet Y)) p x) := by
    intro p p' h x
    subst h
    rfl
  have hU : (mvResUOf K (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom
      (pull (knPrY Y 0) (0 + m) aV
        + cohCast hk (cup (pull (knPrS Y 0) 0 (KnHemi.zeroGenOf K))
            (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU - aV)))))
      = pull (zPrSub Y (zPosSet Y)) (0 + m) aU := by
    rw [map_add, mvResUOf_pull_knPrY, CharClass.cohCast_self, mvResUOf_eq_pull,
      cohPullbackK_apply_eq, pull_cup, pull_sInclusion_zeroGen_posOf,
      pull_sInclusion_knPrY_posOf, one_cup', hpc, CharClass.cohCast_cohCast,
      CharClass.cohCast_self, ← pull_add, add_sub_cancel]
  have hV : (mvResVOf K (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom
      (pull (knPrY Y 0) (0 + m) aV
        + cohCast hk (cup (pull (knPrS Y 0) 0 (KnHemi.zeroGenOf K))
            (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU - aV)))))
      = pull (zPrSub Y (zNegSet Y)) (0 + m) aV := by
    rw [map_add, mvResVOf_pull_knPrY, CharClass.cohCast_self, mvResVOf_eq_pull,
      cohPullbackK_apply_eq, pull_cup, pull_sInclusion_zeroGen_negOf, zero_cup, add_zero]
  have hzero := mvResPairOf_eq_zero_of_disjoint K (zPos Y) (zNeg Y) (z_sup Y) (0 + m)
    (x := z - (pull (knPrY Y 0) (0 + m) aV
        + cohCast hk (cup (pull (knPrS Y 0) 0 (KnHemi.zeroGenOf K))
            (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU - aV))))))
    (by rw [map_sub, hU, haU, sub_self])
    (by rw [map_sub, hV, haV, sub_self])
  exact sub_eq_zero.1 hzero

end KnZero

end

/-! Audited on every build. -/

#audit_axioms KnZero.knTop_zeroOf

end GroupApproximation.CharClass
