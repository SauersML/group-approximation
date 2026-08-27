import GroupApproximation.Computability.BooneGroupBase
import Mathlib.GroupTheory.PresentedGroup

/-!
# S2c: the base group really is `⟨t, x, y | xy = yx⟩`

`BooneGroupBase` takes the split extension `FreeGroup (ℤ × ℤ) ⋊ ℤ²` as the
*definition* of Simpson's base group, because that makes the two facts carrying
the whole argument --- that `T` is free on `{t(α,β)}` and that
`T ∩ G_{ab}^{MN} = T_{ab}^{MN}` --- structural rather than an appeal to the
Kurosh subgroup theorem, which Mathlib does not have.  The cost of that choice
is deferred to here: the final group cannot be called *finitely presented* until
the split extension is proved isomorphic to the two-generator, one-relator
presentation.

That is what this file does.  `presentedEquiv : PresentedGroup rels ≃* BaseGroup`
where `rels` is the single commutator `x y x⁻¹ y⁻¹`.

The two maps are the obvious ones and each is easy for a different reason.
Forward is `PresentedGroup.toGroup`, which needs only that the relator dies in
`BaseGroup` --- true because the acting group is `ℤ²`.  Backward is
`SemidirectProduct.lift`, which needs a map on each factor plus the conjugation
identity; the free factor goes to conjugates of `t`, matching Simpson's
`t(α,β) = x^{-α} y^{-β} t x^{α} y^{β}`, and the acting factor goes to `x^u y^v`.
That the latter is a homomorphism at all is where the relation is used, through
`Commute.zpow_zpow`.

Checking the two composites is then generator-by-generator: `PresentedGroup.ext`
one way, `SemidirectProduct.hom_ext` the other.
-/

namespace GroupApproximation
namespace BooneGroup

open SemidirectProduct Base

/-- Generators: `0 = t`, `1 = x`, `2 = y`. -/
abbrev Gen := Fin 3

/-- The one relation, `xy = yx`, as a relator. -/
def rels : Set (FreeGroup Gen) :=
  {FreeGroup.of 1 * FreeGroup.of 2 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 2)⁻¹}

/-- Simpson's `G = ⟨t, x, y | xy = yx⟩`, as a presentation. -/
abbrev Pres := PresentedGroup rels

/-- `t`, in the presented group. -/
def T : Pres := PresentedGroup.of 0

/-- `x`, in the presented group. -/
def X : Pres := PresentedGroup.of 1

/-- `y`, in the presented group. -/
def Y : Pres := PresentedGroup.of 2

theorem rel_eq_one :
    ((PresentedGroup.mk rels)
        (FreeGroup.of 1 * FreeGroup.of 2 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 2)⁻¹)
      : Pres) = 1 :=
  PresentedGroup.mk_eq_one_iff.mpr (Subgroup.subset_normalClosure rfl)

theorem commute_XY : Commute X Y := by
  have h : X * Y * X⁻¹ * Y⁻¹ = 1 := by
    have hr := rel_eq_one
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
    exact hr
  show X * Y = Y * X
  calc X * Y = X * Y * X⁻¹ * Y⁻¹ * (Y * X) := by group
    _ = 1 * (Y * X) := by rw [h]
    _ = Y * X := one_mul _

/-- Multiplying two `x^i y^j` words, which is where the relation is used. -/
theorem xy_mul (i j k l : ℤ) :
    X ^ i * Y ^ j * (X ^ k * Y ^ l) = X ^ (i + k) * Y ^ (j + l) := by
  have hc : Commute (Y ^ j) (X ^ k) := commute_XY.symm.zpow_zpow j k
  calc X ^ i * Y ^ j * (X ^ k * Y ^ l)
      = X ^ i * (Y ^ j * X ^ k) * Y ^ l := by group
    _ = X ^ i * (X ^ k * Y ^ j) * Y ^ l := by rw [hc.eq]
    _ = X ^ (i + k) * Y ^ (j + l) := by rw [zpow_add, zpow_add]; group

/-- The acting `ℤ²` goes to the words `x^u y^v`. -/
def fRight : Multiplicative (ℤ × ℤ) →* Pres where
  toFun m := X ^ (Multiplicative.toAdd m).1 * Y ^ (Multiplicative.toAdd m).2
  map_one' := by simp
  map_mul' a b := (xy_mul _ _ _ _).symm

@[simp] theorem fRight_ofAdd (p : ℤ × ℤ) :
    fRight (Multiplicative.ofAdd p) = X ^ p.1 * Y ^ p.2 := rfl

/-- The free factor goes to the conjugates of `t`, matching Simpson's
`t(α,β) = x^{-α} y^{-β} t x^{α} y^{β}`. -/
def fLeft : FreeGroup (ℤ × ℤ) →* Pres :=
  FreeGroup.lift fun p =>
    (fRight (Multiplicative.ofAdd p))⁻¹ * T * fRight (Multiplicative.ofAdd p)

theorem fLeft_of (p : ℤ × ℤ) :
    fLeft (FreeGroup.of p)
      = (fRight (Multiplicative.ofAdd p))⁻¹ * T * fRight (Multiplicative.ofAdd p) :=
  FreeGroup.lift_apply_of

/-- The conjugation identity `SemidirectProduct.lift` asks for. -/
theorem lift_compat (g : Multiplicative (ℤ × ℤ)) :
    fLeft.comp (shiftHom g).toMonoidHom
      = (MulAut.conj (fRight g)).toMonoidHom.comp fLeft := by
  refine FreeGroup.ext_hom _ _ fun p => ?_
  have hshift : (shiftHom g) (FreeGroup.of p)
      = FreeGroup.of (p - Multiplicative.toAdd g) := by
    show shiftAut (Multiplicative.toAdd g) (FreeGroup.of p) = _
    rw [shiftAut_of]
  have hsub : fRight (Multiplicative.ofAdd (p - Multiplicative.toAdd g))
      = fRight (Multiplicative.ofAdd p) * (fRight g)⁻¹ := by
    rw [← map_inv, ← map_mul]
    congr 1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hshift, fLeft_of,
    hsub, MulAut.conj_apply]
  group

/-- The backward map. -/
def ofBase : BaseGroup →* Pres := SemidirectProduct.lift fLeft fRight lift_compat

/-- The three generators of the presentation, in the base group. -/
def genMap : Gen → BaseGroup
  | 0 => tGen
  | 1 => xGen
  | 2 => yGen

theorem genMap_rel : ∀ r ∈ rels, FreeGroup.lift genMap r = 1 := by
  rintro r rfl
  have hc : xGen * yGen = yGen * xGen := by
    rw [xGen, yGen, sh_mul_sh, sh_mul_sh]
    congr 1
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
  show genMap 1 * genMap 2 * (genMap 1)⁻¹ * (genMap 2)⁻¹ = 1
  show xGen * yGen * xGen⁻¹ * yGen⁻¹ = 1
  rw [hc]
  group

/-- The forward map. -/
def toBase : Pres →* BaseGroup := PresentedGroup.toGroup genMap_rel

@[simp] theorem toBase_T : toBase T = tGen := PresentedGroup.toGroup.of genMap_rel
@[simp] theorem toBase_X : toBase X = xGen := PresentedGroup.toGroup.of genMap_rel
@[simp] theorem toBase_Y : toBase Y = yGen := PresentedGroup.toGroup.of genMap_rel

theorem toBase_fRight (p : ℤ × ℤ) :
    toBase (fRight (Multiplicative.ofAdd p)) = sh p := by
  rw [fRight_ofAdd, map_mul, map_zpow, map_zpow, toBase_X, toBase_Y,
    sh_x_zpow, sh_y_zpow, sh_mul_sh]
  congr 1
  simp

theorem toBase_ofBase : toBase.comp ofBase = MonoidHom.id BaseGroup := by
  refine SemidirectProduct.hom_ext ?_ ?_
  · refine FreeGroup.ext_hom _ _ fun p => ?_
    show toBase (ofBase (SemidirectProduct.inl (FreeGroup.of p)))
      = SemidirectProduct.inl (FreeGroup.of p)
    rw [ofBase, SemidirectProduct.lift_inl, fLeft_of, map_mul, map_mul, map_inv,
      toBase_fRight, toBase_T]
    have hc := sh_conj_tw (-p) ((0 : ℤ), (0 : ℤ))
    have hp : ((0 : ℤ), (0 : ℤ)) - (-p) = p := by simp
    have htg : tw ((0 : ℤ), (0 : ℤ)) = tGen := rfl
    rw [hp, htg] at hc
    have hinvg : ∀ q : ℤ × ℤ, (sh q)⁻¹ = sh (-q) := by
      intro q
      simp only [sh, ← map_inv]
      rfl
    have h2 : (sh (-p))⁻¹ = sh p := by rw [hinvg, neg_neg]
    rw [hinvg p]
    show sh (-p) * tGen * sh p = tw p
    rw [← hc, h2]
  · refine MonoidHom.ext fun m => ?_
    show toBase (ofBase (SemidirectProduct.inr m)) = SemidirectProduct.inr m
    rw [ofBase, SemidirectProduct.lift_inr]
    exact toBase_fRight (Multiplicative.toAdd m)

theorem ofBase_toBase : ofBase.comp toBase = MonoidHom.id Pres := by
  refine PresentedGroup.ext fun x => ?_
  fin_cases x
  · show ofBase (toBase T) = T
    rw [toBase_T, tGen, tw, ofBase, SemidirectProduct.lift_inl, fLeft_of]
    simp
  · show ofBase (toBase X) = X
    rw [toBase_X, xGen, sh, ofBase, SemidirectProduct.lift_inr]
    simp
  · show ofBase (toBase Y) = Y
    rw [toBase_Y, yGen, sh, ofBase, SemidirectProduct.lift_inr]
    simp

/-- **S2c.**  The split extension is Simpson's presented group. -/
def presentedEquiv : Pres ≃* BaseGroup where
  toFun := toBase
  invFun := ofBase
  left_inv x := congrArg (fun f : Pres →* Pres => f x) ofBase_toBase
  right_inv g := congrArg (fun f : BaseGroup →* BaseGroup => f g) toBase_ofBase
  map_mul' := map_mul toBase

end BooneGroup
end GroupApproximation
