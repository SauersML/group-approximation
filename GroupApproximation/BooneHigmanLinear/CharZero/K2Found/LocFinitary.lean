import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.Colimit
import Mathlib.RingTheory.Localization.Away.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg groups of a localization are finitary (k2-poly, piece F.5)

Let `S` be the localization of a commutative ring `A` at a submonoid `M`. Then `S` is the directed
colimit of the rings `A[1/m]`, `m ∈ M`, preordered by divisibility (`DivIdx M`). The colimit
lemmas of `K2Found/Colimit.lean` give:

* `exists_mem_ringMap_eq_one`: if `u ∈ St_I(A)` dies in `St_I(S)`, there is one `m ∈ M` such
  that `u` dies in `St_I(T)` for every ring map `f : A → T` with `f m` a unit;
* `exists_mem_ringMap_eq`: every element of `St_I(S)` comes from `St_I(A[1/m])` for some
  `m ∈ M`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic

section LocFinitary

variable {A : Type*} [CommRing A] (M : Submonoid A)

/-- The elements of `M`, preordered by divisibility. -/
structure DivIdx where
  /-- The element of `A`. -/
  val : A
  mem : val ∈ M

instance : Preorder (DivIdx M) where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder (DivIdx M) :=
  ⟨fun a b => ⟨⟨a.val * b.val, M.mul_mem a.mem b.mem⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty (DivIdx M) :=
  ⟨⟨1, M.one_mem⟩⟩

/-- `A[1/a] → A[1/b]` for `a ∣ b`. -/
noncomputable def divMap (a b : DivIdx M) (h : a ≤ b) :
    Localization.Away a.val →+* Localization.Away b.val :=
  IsLocalization.Away.lift a.val
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away b.val) b.val h)

theorem divMap_comp (a b : DivIdx M) (h : a ≤ b) :
    (divMap M a b h).comp (algebraMap A (Localization.Away a.val)) =
      algebraMap A (Localization.Away b.val) :=
  IsLocalization.Away.lift_comp _ _

#audit_axioms divMap_comp

theorem divMap_algebraMap (a b : DivIdx M) (h : a ≤ b) (r : A) :
    divMap M a b h (algebraMap A (Localization.Away a.val) r) =
      algebraMap A (Localization.Away b.val) r :=
  IsLocalization.Away.lift_eq _ _ _

#audit_axioms divMap_algebraMap

instance divSystem :
    DirectedSystem (fun a : DivIdx M => Localization.Away a.val)
      (fun a b h => divMap M a b h) where
  map_self a z := by
    have h : divMap M a a le_rfl = RingHom.id _ :=
      IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => by
        simp only [RingHom.comp_apply, divMap_algebraMap, RingHom.id_apply])
    exact RingHom.congr_fun h z
  map_map c b a hab hbc z := by
    have h : (divMap M b c hbc).comp (divMap M a b hab) = divMap M a c (hab.trans hbc) :=
      IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => by
        simp only [RingHom.comp_apply, divMap_algebraMap])
    exact RingHom.congr_fun h z

variable (S : Type*) [CommRing S] [Algebra A S] [IsLocalization M S]

/-- `A[1/a] → S` for `a ∈ M`. -/
noncomputable def locLift (a : DivIdx M) : Localization.Away a.val →+* S :=
  IsLocalization.Away.lift a.val (IsLocalization.map_units S (⟨a.val, a.mem⟩ : M))

theorem locLift_comp (a : DivIdx M) :
    (locLift M S a).comp (algebraMap A (Localization.Away a.val)) = algebraMap A S :=
  IsLocalization.Away.lift_comp _ _

#audit_axioms locLift_comp

theorem locLift_algebraMap (a : DivIdx M) (r : A) :
    locLift M S a (algebraMap A (Localization.Away a.val) r) = algebraMap A S r :=
  IsLocalization.Away.lift_eq _ _ _

#audit_axioms locLift_algebraMap

theorem locLift_divMap (a b : DivIdx M) (h : a ≤ b) (z : Localization.Away a.val) :
    locLift M S b (divMap M a b h z) = locLift M S a z := by
  have hc : (locLift M S b).comp (divMap M a b h) = locLift M S a :=
    IsLocalization.ringHom_ext (Submonoid.powers a.val) (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, divMap_algebraMap, locLift_algebraMap])
  exact RingHom.congr_fun hc z

#audit_axioms locLift_divMap

/-- Two elements with the same image in `S` agree in some `A[1/b]`. -/
theorem locLift_inj (a : DivIdx M) (z w : Localization.Away a.val)
    (h : locLift M S a z = locLift M S a w) :
    ∃ b, ∃ hab : a ≤ b, divMap M a b hab z = divMap M a b hab w := by
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj a.val (z - w)
  have h0 : algebraMap A S c = 0 := by
    have h1 := congrArg (locLift M S a) hc
    rw [map_mul, map_sub, h, sub_self, zero_mul, locLift_algebraMap] at h1
    exact h1.symm
  obtain ⟨⟨t, ht⟩, htc⟩ := (IsLocalization.map_eq_zero_iff (M := M) (S := S) c).mp h0
  have htc' : t * c = 0 := htc
  obtain ⟨b, hbv⟩ : ∃ b : DivIdx M, b.val = a.val * t := ⟨⟨a.val * t, M.mul_mem a.mem ht⟩, rfl⟩
  have hab : a ≤ b := by
    change a.val ∣ b.val
    rw [hbv]
    exact dvd_mul_right _ _
  have htb : t ∣ b.val := by
    rw [hbv]
    exact dvd_mul_left _ _
  refine ⟨b, hab, ?_⟩
  have hb := congrArg (divMap M a b hab) hc
  rw [map_mul, map_pow, divMap_algebraMap, divMap_algebraMap] at hb
  have hct : algebraMap A (Localization.Away b.val) c = 0 := by
    have h1 : algebraMap A (Localization.Away b.val) t *
        algebraMap A (Localization.Away b.val) c = 0 := by
      rw [← map_mul, htc', map_zero]
    exact ((IsLocalization.Away.isUnit_of_dvd (S := Localization.Away b.val) b.val
      htb).mul_right_eq_zero).mp h1
  rw [hct] at hb
  rw [← sub_eq_zero, ← map_sub]
  exact (((IsLocalization.Away.isUnit_of_dvd (S := Localization.Away b.val) b.val
    hab).pow n).mul_left_eq_zero).mp hb

#audit_axioms locLift_inj

/-- Every element of `S` comes from some `A[1/a]`. -/
theorem locLift_surj (s : S) : ∃ a : DivIdx M, ∃ r : Localization.Away a.val,
    locLift M S a r = s := by
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj M s
  refine ⟨⟨y, y.2⟩, IsLocalization.mk' (Localization.Away (y : A)) x
    (⟨y, Submonoid.mem_powers _⟩ : Submonoid.powers (y : A)), ?_⟩
  have h1 := congrArg (locLift M S ⟨y, y.2⟩) (IsLocalization.mk'_spec
    (S := Localization.Away (y : A)) x (⟨y, Submonoid.mem_powers _⟩ : Submonoid.powers (y : A)))
  rw [map_mul, locLift_algebraMap, locLift_algebraMap] at h1
  exact (IsLocalization.map_units S y).mul_left_inj.mp (h1.trans hxy.symm)

#audit_axioms locLift_surj

end LocFinitary

section Main

variable {A : Type*} [CommRing A] (M : Submonoid A) (I : Type*) [Fintype I] [DecidableEq I]
  {S : Type*} [CommRing S] [Algebra A S]

/-- **Finitary form.** If `u ∈ St_I(A)` dies in `St_I(S)`, `S` a localization at `M`, then some
`m ∈ M` kills it: `u` dies along every ring map that makes `m` a unit. -/
theorem exists_mem_ringMap_eq_one (hL : IsLocalization M S) {u : SteinbergGroup I A}
    (hu : ringMap (algebraMap A S) u = 1) :
    ∃ m ∈ M, ∀ (T : Type*) [CommRing T] (f : A →+* T), IsUnit (f m) → ringMap f u = 1 := by
  obtain ⟨i0⟩ : Nonempty (DivIdx M) := inferInstance
  have hu0 : ringMap (locLift M S i0)
      (ringMap (algebraMap A (Localization.Away i0.val)) u) = 1 := by
    rw [ringMap_ringMap, locLift_comp]
    exact hu
  obtain ⟨j, hj, hju⟩ := exists_ringMap_eq_one (R := fun a : DivIdx M => Localization.Away a.val)
    (φ := divMap M) (locLift M S) (locLift_divMap M S) (locLift_inj M S) (locLift_surj M S) hu0
  rw [ringMap_ringMap, divMap_comp] at hju
  refine ⟨j.val, j.mem, fun T _ f hf => ?_⟩
  rw [← IsLocalization.Away.lift_comp (S := Localization.Away j.val) j.val hf, ← ringMap_ringMap,
    hju, map_one]

#audit_axioms exists_mem_ringMap_eq_one

/-- **Surjective form.** Every element of `St_I(S)` comes from `St_I(A[1/m])` for some `m ∈ M`. -/
theorem exists_mem_ringMap_eq (hL : IsLocalization M S) (v : SteinbergGroup I S) :
    ∃ m ∈ M, ∃ u : SteinbergGroup I (Localization.Away m), ∃ f : Localization.Away m →+* S,
      f.comp (algebraMap A (Localization.Away m)) = algebraMap A S ∧ ringMap f u = v := by
  obtain ⟨j, u, hu⟩ := exists_ringMap_eq (R := fun a : DivIdx M => Localization.Away a.val)
    (φ := divMap M) (locLift M S) (locLift_divMap M S) (locLift_surj M S) v
  exact ⟨j.val, j.mem, u, locLift M S j, locLift_comp M S j, hu⟩

#audit_axioms exists_mem_ringMap_eq

end Main

end K2Found
end BooneHigmanLinear
end GroupApproximation
