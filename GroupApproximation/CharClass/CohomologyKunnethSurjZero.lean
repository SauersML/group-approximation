import GroupApproximation.CharClass.CohomologyKunnethSurjStep
import GroupApproximation.CharClass.CohomologyKunnethZero
import GroupApproximation.CharClass.MayerVietorisDisjoint

/-!
# The base of the Künneth decomposition: the zero sphere

`Y × S⁰` is covered by two **disjoint** opens, each homotopy equivalent to `Y`
through the projection, so cohomology splits and a class is determined by its two
restrictions.  The generator `zeroGen` restricts to `1` on one piece and to `0` on
the other, which is exactly what makes `pr_Y^* a + zeroGen ⌣ pr_Y^* b` hit every
pair of restrictions: take `a` the second restriction and `b` the sum of the two.

## Main declarations

* `KnZero.zPos`, `KnZero.zNeg`, `KnZero.z_sup` — the disjoint cover.
* `KnZero.zPrSub` — the projection of a piece to `Y`.
* `KnZero.mvResU_sphereZeroGen`, `KnZero.mvResV_sphereZeroGen` — the generator is
  `1` on one piece and `0` on the other.
* `KnZero.knTop_zero` — the base case.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnZero

variable (Y : Type) [TopologicalSpace Y]

/-! ## 1. The disjoint cover of `Y × S⁰` -/

/-- `Y × S⁰` as an object of `TopCat`. -/
abbrev zProdTop : TopCat.{0} := TopCat.of (Y × Sphere 0)

abbrev zPos : Opens ↥(zProdTop Y) := prodOpen Y sphereZeroPos
abbrev zNeg : Opens ↥(zProdTop Y) := prodOpen Y sphereZeroNeg
abbrev zPosSet : Set ↥(zProdTop Y) := (zPos Y : Set ↥(zProdTop Y))
abbrev zNegSet : Set ↥(zProdTop Y) := (zNeg Y : Set ↥(zProdTop Y))

theorem z_sup : zPos Y ⊔ zNeg Y = ⊤ := prodOpen_sup Y sphereZero_sup

instance isEmpty_z_inter : IsEmpty ↥(zPosSet Y ∩ zNegSet Y) := by
  refine Set.isEmpty_coe_sort.2 ?_
  rw [prodOpen_coe_inter, sphereZero_inter_empty, Set.preimage_empty]

/-! ## 2. The projection of a piece to `Y` -/

/-- The projection to `Y` of a subspace of `Y × S⁰`. -/
def zPrSub (S : Set ↥(zProdTop Y)) : TopCat.of ↥S ⟶ TopCat.of Y :=
  cmap ⟨fun p => (p : Y × Sphere 0).1, continuous_fst.comp continuous_subtype_val⟩

theorem sInclusion_comp_zPrSub (S : Set ↥(zProdTop Y)) :
    sInclusion S ≫ knPrY Y 0 = zPrSub Y S := rfl

/-- The positive piece is `Y`. -/
def zPosHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(zPosSet Y) Y :=
  (prodSubtypeHomeo Y
      ((sphereZeroPos : Opens (Sphere 0)) : Set (Sphere 0))).toHomotopyEquiv.trans
    (prodContractibleEquiv Y
      ↥((sphereZeroPos : Opens (Sphere 0)) : Set (Sphere 0)))

/-- The negative piece is `Y`. -/
def zNegHomotopyEquiv : ContinuousMap.HomotopyEquiv ↥(zNegSet Y) Y :=
  (prodSubtypeHomeo Y
      ((sphereZeroNeg : Opens (Sphere 0)) : Set (Sphere 0))).toHomotopyEquiv.trans
    (prodContractibleEquiv Y
      ↥((sphereZeroNeg : Opens (Sphere 0)) : Set (Sphere 0)))

theorem zPrSub_pos_eq :
    zPrSub Y (zPosSet Y) = cmap (zPosHomotopyEquiv Y).toFun :=
  (TopCat.Hom.ext (by ext p; rfl)).symm

theorem zPrSub_neg_eq :
    zPrSub Y (zNegSet Y) = cmap (zNegHomotopyEquiv Y).toFun :=
  (TopCat.Hom.ext (by ext p; rfl)).symm

theorem exists_pull_zPrSub_pos (m : ℕ) (a : Hmod2 (TopCat.of ↥(zPosSet Y)) m) :
    ∃ c : Hmod2 (TopCat.of Y) m, pull (zPrSub Y (zPosSet Y)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquiv (zPosHomotopyEquiv Y) m).symm a, ?_⟩
  rw [zPrSub_pos_eq]
  exact (pullEquivOfHomotopyEquiv (zPosHomotopyEquiv Y) m).apply_symm_apply a

theorem exists_pull_zPrSub_neg (m : ℕ) (a : Hmod2 (TopCat.of ↥(zNegSet Y)) m) :
    ∃ c : Hmod2 (TopCat.of Y) m, pull (zPrSub Y (zNegSet Y)) m c = a := by
  refine ⟨(pullEquivOfHomotopyEquiv (zNegHomotopyEquiv Y) m).symm a, ?_⟩
  rw [zPrSub_neg_eq]
  exact (pullEquivOfHomotopyEquiv (zNegHomotopyEquiv Y) m).apply_symm_apply a

/-! ## 3. The two restrictions -/

theorem mvResU_pull_knPrY (k : ℕ) (a : Hmod2 (TopCat.of Y) k) :
    (mvResU (zPos Y) (zNeg Y) (z_sup Y) k).hom (pull (knPrY Y 0) k a)
      = pull (zPrSub Y (zPosSet Y)) k a := by
  rw [mvResU_eq_pull, cohPullback_apply_eq, ← pull_comp, sInclusion_comp_zPrSub]

theorem mvResV_pull_knPrY (k : ℕ) (a : Hmod2 (TopCat.of Y) k) :
    (mvResV (zPos Y) (zNeg Y) (z_sup Y) k).hom (pull (knPrY Y 0) k a)
      = pull (zPrSub Y (zNegSet Y)) k a := by
  rw [mvResV_eq_pull, cohPullback_apply_eq, ← pull_comp, sInclusion_comp_zPrSub]

/-- The positive piece maps to the positive point of `S⁰`. -/
def zPosToPos : TopCat.of ↥(zPosSet Y)
    ⟶ TopCat.of ((KnHemi.szPos : Set ↥(TopCat.of (Sphere 0)))) :=
  cmap ⟨fun p => ⟨(p : Y × Sphere 0).2, p.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

/-- The negative piece maps to the negative point of `S⁰`. -/
def zNegToNeg : TopCat.of ↥(zNegSet Y)
    ⟶ TopCat.of ((KnHemi.szNeg : Set ↥(TopCat.of (Sphere 0)))) :=
  cmap ⟨fun p => ⟨(p : Y × Sphere 0).2, p.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

theorem zPosToPos_comp :
    zPosToPos Y ≫ sInclusion (KnHemi.szPos : Set ↥(TopCat.of (Sphere 0)))
      = sInclusion (zPosSet Y) ≫ knPrS Y 0 := rfl

theorem zNegToNeg_comp :
    zNegToNeg Y ≫ sInclusion (KnHemi.szNeg : Set ↥(TopCat.of (Sphere 0)))
      = sInclusion (zNegSet Y) ≫ knPrS Y 0 := rfl

theorem pull_sInclusion_zeroGen_pos :
    pull (sInclusion (zPosSet Y)) 0 (pull (knPrS Y 0) 0 KnHemi.zeroGen)
      = one (TopCat.of ↥(zPosSet Y)) := by
  have hres : pull (sInclusion (KnHemi.szPos : Set ↥(TopCat.of (Sphere 0)))) 0
      KnHemi.zeroGen = one (mvU KnHemi.szPos) := by
    rw [← cohPullback_apply_eq, ← mvResU_eq_pull]
    exact KnHemi.mvResU_zeroGen
  rw [← pull_comp, ← zPosToPos_comp, pull_comp, hres, pull_one]

theorem pull_sInclusion_zeroGen_neg :
    pull (sInclusion (zNegSet Y)) 0 (pull (knPrS Y 0) 0 KnHemi.zeroGen) = 0 := by
  have hres : pull (sInclusion (KnHemi.szNeg : Set ↥(TopCat.of (Sphere 0)))) 0
      KnHemi.zeroGen = 0 := by
    rw [← cohPullback_apply_eq, ← mvResV_eq_pull]
    exact KnHemi.mvResV_zeroGen
  rw [← pull_comp, ← zNegToNeg_comp, pull_comp, hres, pull_zero]

theorem pull_sInclusion_knPrY_pos (S : Set ↥(zProdTop Y)) (k : ℕ)
    (a : Hmod2 (TopCat.of Y) k) :
    pull (sInclusion S) k (pull (knPrY Y 0) k a) = pull (zPrSub Y S) k a := by
  rw [← pull_comp, sInclusion_comp_zPrSub]

theorem mvResU_sphereZeroGen :
    (mvResU (zPos Y) (zNeg Y) (z_sup Y) 0).hom
        (pull (knPrS Y 0) 0 KnHemi.zeroGen)
      = one (TopCat.of ↥(zPosSet Y)) := by
  have hres : pull (sInclusion (KnHemi.szPos : Set ↥(TopCat.of (Sphere 0)))) 0
      KnHemi.zeroGen = one (mvU KnHemi.szPos) := by
    rw [← cohPullback_apply_eq, ← mvResU_eq_pull]
    exact KnHemi.mvResU_zeroGen
  rw [mvResU_eq_pull, cohPullback_apply_eq, ← pull_comp, ← zPosToPos_comp, pull_comp,
    hres, pull_one]

theorem mvResV_sphereZeroGen :
    (mvResV (zPos Y) (zNeg Y) (z_sup Y) 0).hom
        (pull (knPrS Y 0) 0 KnHemi.zeroGen) = 0 := by
  have hres : pull (sInclusion (KnHemi.szNeg : Set ↥(TopCat.of (Sphere 0)))) 0
      KnHemi.zeroGen = 0 := by
    rw [← cohPullback_apply_eq, ← mvResV_eq_pull]
    exact KnHemi.mvResV_zeroGen
  rw [mvResV_eq_pull, cohPullback_apply_eq, ← pull_comp, ← zNegToNeg_comp, pull_comp,
    hres, pull_zero]

/-! ## 4. The base case -/

theorem add_add_self_left {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x + (y + x) = y := by
  rw [add_comm y x, ← add_assoc, add_self_eq_zero_two, zero_add]

set_option maxHeartbeats 1000000 in
/-- **The base of the Künneth decomposition.** -/
theorem knTop_zero : KnHemi.KnTop 0 KnHemi.zeroGen := by
  intro Y _ k m hk z
  obtain rfl : k = 0 + m := hk.symm
  obtain ⟨aU, haU⟩ := exists_pull_zPrSub_pos Y (0 + m)
    ((mvResU (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom z)
  obtain ⟨aV, haV⟩ := exists_pull_zPrSub_neg Y (0 + m)
    ((mvResV (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom z)
  refine ⟨aV, cohCast (Nat.zero_add m) (aU + aV), ?_⟩
  have hU : (mvResU (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom
      (pull (knPrY Y 0) (0 + m) aV
        + cohCast hk (cup (pull (knPrS Y 0) 0 KnHemi.zeroGen)
            (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU + aV)))))
      = pull (zPrSub Y (zPosSet Y)) (0 + m) aU := by
    rw [map_add, mvResU_pull_knPrY, cohCast_self, mvResU_eq_pull, cohPullback_apply_eq,
      pull_cup, pull_sInclusion_zeroGen_pos, pull_sInclusion_knPrY_pos, one_cup',
      KnHemi.pull_cohCast, cohCast_cohCast, cohCast_self, ← pull_add,
      add_add_self_left]
  have hV : (mvResV (zPos Y) (zNeg Y) (z_sup Y) (0 + m)).hom
      (pull (knPrY Y 0) (0 + m) aV
        + cohCast hk (cup (pull (knPrS Y 0) 0 KnHemi.zeroGen)
            (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU + aV)))))
      = pull (zPrSub Y (zNegSet Y)) (0 + m) aV := by
    rw [map_add, mvResV_pull_knPrY, cohCast_self, mvResV_eq_pull, cohPullback_apply_eq,
      pull_cup, pull_sInclusion_zeroGen_neg, zero_cup, add_zero]
  have hzero := mvResPair_eq_zero_of_disjoint (zPos Y) (zNeg Y) (z_sup Y) (0 + m)
    (x := z + (pull (knPrY Y 0) (0 + m) aV
        + cohCast hk (cup (pull (knPrS Y 0) 0 KnHemi.zeroGen)
            (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU + aV))))))
    (by rw [map_add, hU, haU, add_self_eq_zero_two])
    (by rw [map_add, hV, haV, add_self_eq_zero_two])
  have hfin := congrArg (fun y => y + (pull (knPrY Y 0) (0 + m) aV
      + cohCast hk (cup (pull (knPrS Y 0) 0 KnHemi.zeroGen)
          (pull (knPrY Y 0) m (cohCast (Nat.zero_add m) (aU + aV))))))
    hzero
  simpa only [add_assoc, add_self_eq_zero_two, add_zero, zero_add] using hfin

end KnZero

end

end GroupApproximation.CharClass
