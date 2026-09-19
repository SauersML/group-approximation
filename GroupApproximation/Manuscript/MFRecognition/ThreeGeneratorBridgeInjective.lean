import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridgeNormalCore
import GroupApproximation.Sofic.FreeGroupResiduallyFinite
import GroupApproximation.Sofic.ThreeRadicalsCoincide

/-!
# The three-generator bridge, part 5: clause (3) of `lem:bridge`

This file formalizes clause (3) of `lem:bridge` of
`mf_recognition_complexity.tex` and its printed proof:

> (3) The assignment `x ↦ (x_1,x_2)`, `y ↦ (y,1)`, `t ↦ (1,t)` defines an
> injective homomorphism `j : Q_+ → P = F(x_1,y) × F(x_2,t)`.  In particular,
> `Q_+` is residually finite.

> (3) The relators `[t,y_i]` are sent to `[(1,t),(x_1^i y x_1^{-i},1)] = 1`, so
> `j` is a homomorphism.  Let `N_0` be the normal closure of `{y,t}` in `Q_+`.
> Then `Q_+/N_0 = ⟨x⟩` is infinite cyclic and the extension splits, so
> `Q_+ = N_0 ⋊ ⟨x⟩`.  ...  So `N_0 = F(y_n) × F(t_m)`.  Now
> `j(y_n) = (x_1^n y x_1^{-n},1)` and `j(t_m) = (1, x_2^m t x_2^{-m})`, and the
> elements `x_1^n y x_1^{-n}` freely generate the normal closure of `y` in
> `F(x_1,y)`, and likewise for `t`; so `j` restricted to `N_0` is an isomorphism
> onto the product of these two normal closures.  Finally `j(x) = (x_1,x_2)` has
> infinite order and `j(x)^k ∉ j(N_0)` for `k ≠ 0`, because, for `h ∈ N_0`, the
> exponent sum of `x_1` in `j(x^k h)` is `k`.  So `j` is injective on
> `N_0 ⋊ ⟨x⟩`.  Free groups are residually finite and residual finiteness passes
> to direct products and subgroups, so `Q_+` is residually finite.

The steps appear in the printed order:

* `jQ` --- the homomorphism, well defined because the second coordinate of the
  image of every `y_i` is trivial (`jSnd_yBaseHom`), so `(1,t)` commutes with it;
* `exists_split` (in `ThreeGeneratorBridgeNormalCore`) --- the splitting;
* `nzeroModel_eq_Nzero` and `Theta_injective` --- `N_0 = F(y_n) × F(t_m)`;
* `jQFst_Theta`, `jQSnd_Theta` --- `j` on `N_0` is the product of the two
  normal-closure isomorphisms of `range_yFreeHom_eq_normalClosure`;
* `epsQ_split` --- the exponent-sum step;
* `jQ_injective`, `qplus_isResiduallyFinite`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Bridge

open GroupApproximation.Higman.HNNEmb
open GroupApproximation.Higman

/-! ## 1.  The target `P = F(x_1,y) × F(x_2,t)` -/

/-- **`P = F(x_1,y) × F(x_2,t)`.**  In the first factor the printed generators
are `x_1 = 0` and `y = 1`; in the second, `x_2 = 0` and `t = 1`. -/
abbrev Pprod : Type := FreeXY × FreeXY

/-- The printed assignment on the two free generators of the base:
`x ↦ (x_1,x_2)` and `y ↦ (y,1)`. -/
def jTwo : Fin 2 → Pprod := fun i => if i = 0 then (xTwo, xTwo) else (yTwo, 1)

/-- The printed assignment, on the base `1 * F(x,y)` of `Q_+`. -/
def jBase : Higman.HNNEmb.P Triv →* Pprod :=
  Monoid.Coprod.lift 1 (FreeGroup.lift jTwo)

theorem jBase_iF (v : FreeXY) :
    jBase (iF v : Higman.HNNEmb.P Triv) = FreeGroup.lift jTwo v := by
  show (Monoid.Coprod.lift (1 : Triv →* Pprod) (FreeGroup.lift jTwo))
      (Monoid.Coprod.inr v) = (FreeGroup.lift jTwo : FreeXY →* Pprod) v
  rw [Monoid.Coprod.lift_apply_inr]

theorem jBase_xg : jBase (xg : Higman.HNNEmb.P Triv) = (xTwo, xTwo) := by
  show jBase (iF xTwo : Higman.HNNEmb.P Triv) = (xTwo, xTwo)
  rw [jBase_iF]
  simp [jTwo, xTwo]

theorem jBase_yg : jBase (yg : Higman.HNNEmb.P Triv) = (yTwo, 1) := by
  show jBase (iF yTwo : Higman.HNNEmb.P Triv) = (yTwo, 1)
  rw [jBase_iF]
  simp [jTwo, yTwo]

/-- The second coordinate of the printed assignment on the base. -/
def jSnd : Higman.HNNEmb.P Triv →* FreeXY := (MonoidHom.snd FreeXY FreeXY).comp jBase

theorem jSnd_xg : jSnd (xg : Higman.HNNEmb.P Triv) = xTwo := congrArg Prod.snd jBase_xg

theorem jSnd_yg : jSnd (yg : Higman.HNNEmb.P Triv) = 1 := congrArg Prod.snd jBase_yg

/-- **"The relators `[t,y_i]` are sent to `[(1,t),(x_1^i y x_1^{-i},1)] = 1`."**
The second coordinate of the image of every `y_i` is trivial. -/
theorem jSnd_yBase (i : ℤ) : jSnd (yBase Triv i) = 1 := by
  show jSnd ((xg : Higman.HNNEmb.P Triv) ^ i * yg * (xg : Higman.HNNEmb.P Triv) ^ (-i)) = 1
  rw [map_mul, map_mul, map_zpow, map_zpow, jSnd_xg, jSnd_yg, mul_one, ← zpow_add,
    add_neg_cancel, zpow_zero]

theorem jSnd_yBaseHom (W : FreeGroup ℤ) : jSnd (yBaseHom Triv W) = 1 := by
  refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
  · simp only [map_one]
  · intro i
    rw [yBaseHom_of]
    exact jSnd_yBase i
  · intro i h
    rw [map_inv, map_inv, h, inv_one]
  · intro u v hu hv
    rw [map_mul, map_mul, hu, hv, mul_one]

theorem jBase_commute (W : FreeGroup ℤ) :
    ((1 : FreeXY), yTwo) * jBase (yBaseHom Triv W)
      = jBase (yBaseHom Triv W) * ((1 : FreeXY), yTwo) := by
  refine Prod.ext ?_ ?_
  · show (1 : FreeXY) * (jBase (yBaseHom Triv W)).1
      = (jBase (yBaseHom Triv W)).1 * 1
    rw [one_mul, mul_one]
  · show yTwo * jSnd (yBaseHom Triv W) = jSnd (yBaseHom Triv W) * yTwo
    rw [jSnd_yBaseHom, mul_one, one_mul]

/-- **`j : Q_+ → P`.**  "The assignment `x ↦ (x_1,x_2)`, `y ↦ (y,1)`,
`t ↦ (1,t)` defines a homomorphism." -/
noncomputable def jQ : Qplus →* Pprod :=
  HNNExtension.lift jBase ((1 : FreeXY), yTwo) (fun a => by
    rw [bridgePsi_triv a]
    obtain ⟨W, hW⟩ := exists_yBaseHom a
    rw [hW]
    exact jBase_commute W)

theorem jQ_of (u : Higman.HNNEmb.P Triv) : jQ (HNNExtension.of u) = jBase u :=
  HNNExtension.lift_of _ _ _ _

theorem jQ_t : jQ (HNNExtension.t : Qplus) = ((1 : FreeXY), yTwo) :=
  HNNExtension.lift_t _ _ _

theorem jQ_qx : jQ qx = (xTwo, xTwo) := by
  rw [qx_eq, jQ_of, jBase_xg]

theorem jQ_qy : jQ qy = (yTwo, 1) := by
  rw [qy_eq, jQ_of, jBase_yg]

theorem jQ_qt : jQ qt = ((1 : FreeXY), yTwo) := by
  rw [qt_eq, jQ_t]

/-! ## 2.  The two coordinates of `j` -/

/-- The first coordinate of `j`, landing in `F(x_1,y)`. -/
noncomputable def jQFst : Qplus →* FreeXY := (MonoidHom.fst FreeXY FreeXY).comp jQ

/-- The second coordinate of `j`, landing in `F(x_2,t)`. -/
noncomputable def jQSnd : Qplus →* FreeXY := (MonoidHom.snd FreeXY FreeXY).comp jQ

theorem jQ_eq_one_iff (u : Qplus) : jQ u = 1 ↔ jQFst u = 1 ∧ jQSnd u = 1 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2

theorem jQFst_qx : jQFst qx = xTwo := congrArg Prod.fst jQ_qx

theorem jQSnd_qx : jQSnd qx = xTwo := congrArg Prod.snd jQ_qx

theorem jQFst_qy : jQFst qy = yTwo := congrArg Prod.fst jQ_qy

theorem jQSnd_qy : jQSnd qy = 1 := congrArg Prod.snd jQ_qy

theorem jQFst_qt : jQFst qt = 1 := congrArg Prod.fst jQ_qt

theorem jQSnd_qt : jQSnd qt = yTwo := congrArg Prod.snd jQ_qt

/-- **"`j(y_n) = (x_1^n y x_1^{-n}, 1)`."** -/
theorem jQFst_qyFam (n : ℤ) : jQFst (qyFam n) = yFree n := by
  show jQFst (qx ^ n * qy * qx ^ (-n)) = xTwo ^ n * yTwo * xTwo ^ (-n)
  rw [map_mul, map_mul, map_zpow, map_zpow, jQFst_qx, jQFst_qy]

theorem jQSnd_qyFam (n : ℤ) : jQSnd (qyFam n) = 1 := by
  show jQSnd (qx ^ n * qy * qx ^ (-n)) = 1
  rw [map_mul, map_mul, map_zpow, map_zpow, jQSnd_qx, jQSnd_qy, mul_one, ← zpow_add,
    add_neg_cancel, zpow_zero]

/-- **"`j(t_m) = (1, x_2^m t x_2^{-m})`."** -/
theorem jQSnd_qtFam (m : ℤ) : jQSnd (qtFam m) = yFree m := by
  show jQSnd (qx ^ m * qt * qx ^ (-m)) = xTwo ^ m * yTwo * xTwo ^ (-m)
  rw [map_mul, map_mul, map_zpow, map_zpow, jQSnd_qx, jQSnd_qt]

theorem jQFst_qtFam (m : ℤ) : jQFst (qtFam m) = 1 := by
  show jQFst (qx ^ m * qt * qx ^ (-m)) = 1
  rw [map_mul, map_mul, map_zpow, map_zpow, jQFst_qx, jQFst_qt, mul_one, ← zpow_add,
    add_neg_cancel, zpow_zero]

theorem jQFst_comp_qyHom : jQFst.comp qyHom = yFreeHom := by
  refine FreeGroup.ext_hom _ _ fun n => ?_
  show jQFst (qyHom (FreeGroup.of n)) = yFreeHom (FreeGroup.of n)
  rw [qyHom_of, yFreeHom_of, jQFst_qyFam]

theorem jQSnd_comp_qtHom : jQSnd.comp qtHom = yFreeHom := by
  refine FreeGroup.ext_hom _ _ fun m => ?_
  show jQSnd (qtHom (FreeGroup.of m)) = yFreeHom (FreeGroup.of m)
  rw [qtHom_of, yFreeHom_of, jQSnd_qtFam]

theorem jQFst_qyHom (a : FreeGroup ℤ) : jQFst (qyHom a) = yFreeHom a :=
  congrArg (fun f : FreeGroup ℤ →* FreeXY => f a) jQFst_comp_qyHom

theorem jQSnd_qtHom (b : FreeGroup ℤ) : jQSnd (qtHom b) = yFreeHom b :=
  congrArg (fun f : FreeGroup ℤ →* FreeXY => f b) jQSnd_comp_qtHom

theorem jQFst_qtHom (b : FreeGroup ℤ) : jQFst (qtHom b) = 1 := by
  refine FreeGroup.induction_on b ?_ ?_ ?_ ?_
  · simp only [map_one]
  · intro m
    rw [qtHom_of]
    exact jQFst_qtFam m
  · intro m h
    rw [map_inv, map_inv, h, inv_one]
  · intro u v hu hv
    rw [map_mul, map_mul, hu, hv, mul_one]

theorem jQSnd_qyHom (a : FreeGroup ℤ) : jQSnd (qyHom a) = 1 := by
  refine FreeGroup.induction_on a ?_ ?_ ?_ ?_
  · simp only [map_one]
  · intro n
    rw [qyHom_of]
    exact jQSnd_qyFam n
  · intro n h
    rw [map_inv, map_inv, h, inv_one]
  · intro u v hu hv
    rw [map_mul, map_mul, hu, hv, mul_one]

/-- **"`j` restricted to `N_0` is an isomorphism onto the product of these two
normal closures."**  On `N_0 = F(y_n) × F(t_m)` the map `j` is the product of
two copies of `yFreeHom`, whose range is the printed normal closure by
`range_yFreeHom_eq_normalClosure`. -/
theorem jQFst_Theta (a b : FreeGroup ℤ) : jQFst (Theta (a, b)) = yFreeHom a := by
  rw [Theta_apply, map_mul, jQFst_qyHom, jQFst_qtHom, mul_one]

theorem jQSnd_Theta (a b : FreeGroup ℤ) : jQSnd (Theta (a, b)) = yFreeHom b := by
  rw [Theta_apply, map_mul, jQSnd_qyHom, jQSnd_qtHom, one_mul]

/-- **`lem:bridge` (3).**  "`j` restricted to `N_0` is an isomorphism onto the
product of these two normal closures."  Read through the printed identification
`N_0 = F(y_n) × F(t_m)` of `nzeroModel_eq_Nzero`, the map `j` is `yFreeHom` in
each coordinate; `range_yFreeHom_eq_normalClosure` identifies the image of each
coordinate with the printed normal closure, and `yFreeHom_injective` with
`Theta_injective` make the restriction an isomorphism onto it. -/
theorem jQ_Theta_eq (a b : FreeGroup ℤ) :
    jQ (Theta (a, b)) = (yFreeHom a, yFreeHom b) :=
  Prod.ext (jQFst_Theta a b) (jQSnd_Theta a b)

/-- The printed conclusion of the `N_0` computation, in the form the final
argument consumes: an element of `N_0` killed by `j` is trivial, because each of
its two coordinates is a word in the printed free basis of a normal closure. -/
theorem Theta_eq_one_of_jQ_eq_one {a b : FreeGroup ℤ}
    (hj : jQ (Theta (a, b)) = 1) : Theta (a, b) = 1 := by
  obtain ⟨hf, hs⟩ := (jQ_eq_one_iff _).mp hj
  have h1 : yFreeHom a = 1 := by
    rw [← jQFst_Theta a b]
    exact hf
  have h2 : yFreeHom b = 1 := by
    rw [← jQSnd_Theta a b]
    exact hs
  have ha : a = 1 := yFreeHom_injective (by rw [h1, map_one])
  have hb : b = 1 := yFreeHom_injective (by rw [h2, map_one])
  rw [Theta_apply, ha, hb, map_one, map_one, one_mul]

/-- **`lem:bridge` (3), the Reidemeister--Schreier step, injective half.**  The
map onto `N_0` from the direct product of the two free groups is injective, so
the printed identification `N_0 = F(y_n : n ∈ ℤ) × F(t_m : m ∈ ℤ)` holds. -/
theorem Theta_injective : Function.Injective Theta := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hab
  have hj : jQ (Theta (a, b)) = 1 := by rw [hab, map_one]
  obtain ⟨hf, hs⟩ := (jQ_eq_one_iff _).mp hj
  have h1 : yFreeHom a = 1 := by
    rw [← jQFst_Theta a b]
    exact hf
  have h2 : yFreeHom b = 1 := by
    rw [← jQSnd_Theta a b]
    exact hs
  have ha : a = 1 := yFreeHom_injective (by rw [h1, map_one])
  have hb : b = 1 := yFreeHom_injective (by rw [h2, map_one])
  exact Prod.ext ha hb

/-- **`lem:bridge` (3).**  "So `N_0 = F(y_n : n ∈ ℤ) × F(t_m : m ∈ ℤ)`": the map
from the direct product of the two free groups on the printed families is
injective with image exactly `N_0`. -/
theorem nzero_eq_free_prod :
    Function.Injective Theta ∧ Theta.range = Nzero :=
  ⟨Theta_injective, nzeroModel_eq_Nzero⟩

/-- **`j` is injective on `N_0`.** -/
theorem eq_one_of_jQ_eq_one_of_mem_Nzero {h : Qplus} (hh : h ∈ Nzero)
    (hj : jQ h = 1) : h = 1 := by
  rw [← nzeroModel_eq_Nzero] at hh
  obtain ⟨⟨a, b⟩, rfl⟩ := hh
  exact Theta_eq_one_of_jQ_eq_one hj

/-! ## 3.  The exponent sum of `x_1` -/

/-- The exponent sum of the first generator of `F(x,y)`. -/
def expSum : FreeXY →* Multiplicative ℤ :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then Multiplicative.ofAdd (1 : ℤ) else 1)

theorem expSum_xTwo : expSum xTwo = Multiplicative.ofAdd (1 : ℤ) := by
  simp [expSum, xTwo]

theorem expSum_yTwo : expSum yTwo = 1 := by
  simp [expSum, yTwo]

/-- **The exponent sum of `x_1` in the image of an element of `Q_+`.** -/
noncomputable def epsQ : Qplus →* Multiplicative ℤ := expSum.comp jQFst

theorem epsQ_qx : epsQ qx = Multiplicative.ofAdd (1 : ℤ) := by
  show expSum (jQFst qx) = Multiplicative.ofAdd (1 : ℤ)
  rw [jQFst_qx, expSum_xTwo]

theorem epsQ_qy : epsQ qy = 1 := by
  show expSum (jQFst qy) = 1
  rw [jQFst_qy, expSum_yTwo]

theorem epsQ_qt : epsQ qt = 1 := by
  show expSum (jQFst qt) = 1
  rw [jQFst_qt, map_one]

theorem Nzero_le_ker_epsQ : Nzero ≤ epsQ.ker := by
  haveI := MonoidHom.normal_ker epsQ
  refine Subgroup.normalClosure_le_normal ?_
  rintro z (rfl | rfl)
  · show epsQ qy = 1
    exact epsQ_qy
  · show epsQ qt = 1
    exact epsQ_qt

theorem toAdd_ofAdd_one_zpow (k : ℤ) :
    Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ k) = k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add, zpow_one]
      show Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ (n : ℤ)) + 1
        = (n : ℤ) + 1
      rw [ih]
  | pred n ih =>
      rw [zpow_sub, zpow_one]
      show Multiplicative.toAdd ((Multiplicative.ofAdd (1 : ℤ)) ^ (-(n : ℤ))) + -1
        = -(n : ℤ) + -1
      rw [ih]

theorem zpow_ofAdd_one_eq_one_iff (k : ℤ) :
    (Multiplicative.ofAdd (1 : ℤ)) ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    have hk := toAdd_ofAdd_one_zpow k
    rw [h] at hk
    exact hk.symm
  · intro h
    rw [h, zpow_zero]

/-- **`lem:bridge` (3), the exponent-sum step.**  "For `h ∈ N_0`, the exponent
sum of `x_1` in `j(x^k h)` is `k`." -/
theorem epsQ_split {h : Qplus} (hh : h ∈ Nzero) (k : ℤ) :
    epsQ (h * qx ^ k) = (Multiplicative.ofAdd (1 : ℤ)) ^ k := by
  have h1 : epsQ h = 1 := Nzero_le_ker_epsQ hh
  rw [map_mul, map_zpow, epsQ_qx, h1, one_mul]

/-- **`lem:bridge` (3).**  "`Q_+/N_0 = ⟨x⟩` is infinite cyclic", and the printed
consequence "`j(x)^k ∉ j(N_0)` for `k ≠ 0`": no nonzero power of `x` meets `N_0`,
by the exponent sum of `x_1`. -/
theorem qx_zpow_mem_Nzero_iff (k : ℤ) : qx ^ k ∈ Nzero ↔ k = 0 := by
  constructor
  · intro hk
    have h1 : epsQ (qx ^ k) = 1 := Nzero_le_ker_epsQ hk
    rw [map_zpow, epsQ_qx] at h1
    exact (zpow_ofAdd_one_eq_one_iff k).mp h1
  · intro hk
    rw [hk, zpow_zero]
    exact Subgroup.one_mem _

/-- **`lem:bridge` (3), the printed splitting.**  "Then `Q_+/N_0 = ⟨x⟩` is
infinite cyclic and the extension splits, so `Q_+ = N_0 ⋊ ⟨x⟩`": every element
factors as `h · x^k` with `h ∈ N_0`, and the cyclic complement meets `N_0`
trivially, so the quotient is infinite cyclic and the factorization is
unique. -/
theorem qplus_semidirect :
    (∀ u : Qplus, ∃ h ∈ Nzero, ∃ k : ℤ, u = h * qx ^ k) ∧
      (∀ k : ℤ, qx ^ k ∈ Nzero ↔ k = 0) :=
  ⟨exists_split, qx_zpow_mem_Nzero_iff⟩

/-! ## 4.  Clause (3) -/

/-- **`lem:bridge` (3).**  "The assignment `x ↦ (x_1,x_2)`, `y ↦ (y,1)`,
`t ↦ (1,t)` defines an injective homomorphism
`j : Q_+ → P = F(x_1,y) × F(x_2,t)`." -/
theorem jQ_injective : Function.Injective jQ := by
  rw [injective_iff_map_eq_one]
  intro u hu
  obtain ⟨h, hh, k, rfl⟩ := exists_split u
  obtain ⟨hf, _hs⟩ := (jQ_eq_one_iff _).mp hu
  have hk : (Multiplicative.ofAdd (1 : ℤ)) ^ k = 1 := by
    rw [← epsQ_split hh k]
    show expSum (jQFst (h * qx ^ k)) = 1
    rw [hf, map_one]
  have hk0 : k = 0 := (zpow_ofAdd_one_eq_one_iff k).mp hk
  rw [hk0, zpow_zero, mul_one] at hu ⊢
  exact eq_one_of_jQ_eq_one_of_mem_Nzero hh hu

/-- **`lem:bridge` (3).**  "`j(x) = (x_1,x_2)` has infinite order."  The
operative half of that sentence --- `j(x)^k ∉ j(N_0)` for `k ≠ 0` --- is
`qx_zpow_mem_Nzero_iff`, which the injectivity proof consumes; infinite order
itself is read off afterwards. -/
theorem jQ_qx_zpow_eq_one_iff (k : ℤ) : jQ qx ^ k = 1 ↔ k = 0 := by
  rw [← map_zpow]
  constructor
  · intro h
    have hone : qx ^ k = 1 := jQ_injective (by rw [h, map_one])
    have hmem : qx ^ k ∈ Nzero := by
      rw [hone]
      exact Subgroup.one_mem _
    exact (qx_zpow_mem_Nzero_iff k).mp hmem
  · intro hk
    rw [hk, zpow_zero, map_one]

/-- Mathlib's residual finiteness of free groups, in the development's
predicate. -/
theorem isResiduallyFinite_freeXY : IsResiduallyFinite FreeXY := by
  refine le_antisymm ?_ bot_le
  intro z hz
  rw [Subgroup.mem_bot]
  exact Group.residuallyFinite_iff_forall_finiteIndex.mp inferInstance z
    (fun H hH => mem_finiteResidual_iff.mp hz H hH)

/-- **`lem:bridge` (3), last sentence.**  "Free groups are residually finite and
residual finiteness passes to direct products and subgroups, so `Q_+` is
residually finite." -/
theorem qplus_isResiduallyFinite : IsResiduallyFinite Qplus :=
  IsResiduallyFinite.of_injective jQ jQ_injective
    (isResiduallyFinite_freeXY.prod isResiduallyFinite_freeXY)

/-- **`lem:bridge` (3), packaged.** -/
theorem manuscriptBridge_three :
    jQ qx = (xTwo, xTwo) ∧ jQ qy = (yTwo, 1) ∧ jQ qt = ((1 : FreeXY), yTwo) ∧
      Function.Injective jQ ∧ IsResiduallyFinite Qplus :=
  ⟨jQ_qx, jQ_qy, jQ_qt, jQ_injective, qplus_isResiduallyFinite⟩

/-! ## 5.  The family `Q_e` -/

/-- **The paragraph after `lem:bridge`.**  "For `e ∈ ℕ` let `Q_e = B(C_e) = F/N_e`
with `C_e` the group of Lemma `lem:switch`."  The family `C_e` with its
generating sequences is the input; `lem:switch` supplies it. -/
abbrev Qe {C : ℕ → Type} [∀ e, Group (C e)] (c : ∀ e, ℤ → C e) (e : ℕ) : Type :=
  BGroup (c e)

/-- **`q_e : F → Q_e`.** -/
noncomputable def qe {C : ℕ → Type} [∀ e, Group (C e)] (c : ∀ e, ℤ → C e) (e : ℕ) :
    FreeXYT →* Qe c e := qC (c e)

/-- **`N_e`**, so that `Q_e = F/N_e`.  (Named `NeSub`: `Ne` is taken by core.) -/
noncomputable abbrev NeSub {C : ℕ → Type} [∀ e, Group (C e)]
    (c : ∀ e, ℤ → C e) (e : ℕ) :
    Subgroup FreeXYT := NC (c e)

/-- **The two clauses of that paragraph supplied by `lem:bridge` alone**:
`N_e ≤ N_+`, and `C_e` embeds in `Q_e`.  The remaining clauses --- that a
recursive presentation of `Q_e` on `x,y,t` is computable from `e`, that
`Q_e = Q_+` on `INF`, and that `H ≤ C_e ≤ Q_e` on `FIN` --- combine this with
`lem:switch`. -/
theorem manuscriptQe {C : ℕ → Type} [∀ e, Group (C e)] (c : ∀ e, ℤ → C e) (e : ℕ) :
    NeSub c e ≤ Nplus ∧ Function.Injective (embC (c e)) :=
  ⟨NC_le_Nplus (c e), embC_injective (c e)⟩

/-- **The `INF` branch of that paragraph.**  "If `e ∈ INF` then `Q_e = Q_+`,
`N_e = N_+` and `q_e = q_+`": on the infinite branch `C_e` is trivial, and
`lem:bridge` (2) then gives equality of the kernels. -/
theorem manuscriptQe_trivial {C : ℕ → Type} [∀ e, Group (C e)]
    (c : ∀ e, ℤ → C e) (e : ℕ) (h : Subsingleton (C e)) :
    NeSub c e = Nplus := by
  haveI := h
  exact manuscriptBridge_two_trivial (c e)

end Bridge
end MFRecognition
end Manuscript
end GroupApproximation
