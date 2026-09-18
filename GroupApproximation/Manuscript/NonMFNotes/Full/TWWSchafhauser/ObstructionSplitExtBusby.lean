import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtCorona

/-!
# The Busby map of an Ext cycle

Lane `TWWSch3d4a`, work order `WO-TWWSch-3d4-1` (with `WO-TWWSch-3c-1`), third part.

A cycle `x : BusbyCycle S J` (`ObstructionExt.lean`) is a lift `S → 𝓛(H_J)` of a `⋆`-homomorphism
into the corona algebra, with the homomorphism identities holding modulo compacts. Composing with
the quotient `stdCoronaQuot J` (`ObstructionSplitExtCorona.lean`) gives the **Busby map**
`S → Q(J ⊗ 𝒦)` itself (Busby, Trans. AMS 132 (1968); Blackadar, *K-theory for operator
algebras*, §15.3):

* `BusbyCycle.bddLift x a`: the lift of `a` as a bounded operator;
* `BusbyCycle.busbyₙ x : S →⋆ₙₐ[ℂ] StdCorona J`: the Busby map, a non-unital `⋆`-homomorphism;
* `BusbyCycle.IsUnital x`: the lift of `1` is the identity modulo compacts;
* `BusbyCycle.busby x hx : S →⋆ₐ[ℂ] StdCorona J` for unital `S` and a unital cycle;
* `busbyₙ_apply`, `busby_apply`: the value is `stdCoronaMk (x.lift a)`, the class of the lift;
* `busbyₙ_eq_iff`: two cycles have the same Busby map iff their lifts agree modulo compacts.
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

section NonUnital

variable {S : Type} [NonUnitalCStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The lift of `a` as an element of the bounded operators `StdBdd J`. -/
def BusbyCycle.bddLift (x : BusbyCycle S J) (a : S) : StdBdd J :=
  ⟨x.lift a, mem_boundedAdj.mpr (x.bounded a)⟩

theorem BusbyCycle.bddLift_coe (x : BusbyCycle S J) (a : S) : (x.bddLift a).1 = x.lift a := rfl

/-- The underlying function of the Busby map: the class of the lift in the corona. -/
def BusbyCycle.busbyFun (x : BusbyCycle S J) (a : S) : StdCorona J :=
  stdCoronaQuot J (x.bddLift a)

theorem BusbyCycle.busbyFun_eq_stdCoronaMk (x : BusbyCycle S J) (a : S) :
    x.busbyFun a = stdCoronaMk (x.lift a) :=
  (stdCoronaMk_coe (x.bddLift a)).symm

theorem BusbyCycle.busbyFun_add (x : BusbyCycle S J) (a a' : S) :
    x.busbyFun (a + a') = x.busbyFun a + x.busbyFun a' :=
  ((stdCoronaQuot_eq_iff (x.bddLift (a + a')) (x.bddLift a + x.bddLift a')).mpr
    (x.map_add a a')).trans (map_add (stdCoronaQuot J) (x.bddLift a) (x.bddLift a'))

theorem BusbyCycle.busbyFun_smul (x : BusbyCycle S J) (c : ℂ) (a : S) :
    x.busbyFun (c • a) = c • x.busbyFun a :=
  ((stdCoronaQuot_eq_iff (x.bddLift (c • a)) (c • x.bddLift a)).mpr
    (x.map_smul c a)).trans (map_smul (stdCoronaQuot J) c (x.bddLift a))

theorem BusbyCycle.busbyFun_mul (x : BusbyCycle S J) (a a' : S) :
    x.busbyFun (a * a') = x.busbyFun a * x.busbyFun a' :=
  ((stdCoronaQuot_eq_iff (x.bddLift (a * a')) (x.bddLift a * x.bddLift a')).mpr
    (x.map_mul a a')).trans (map_mul (stdCoronaQuot J) (x.bddLift a) (x.bddLift a'))

theorem BusbyCycle.busbyFun_star (x : BusbyCycle S J) (a : S) :
    x.busbyFun (star a) = star (x.busbyFun a) :=
  ((stdCoronaQuot_eq_iff (x.bddLift (star a)) (star (x.bddLift a))).mpr
    (x.map_star a)).trans (map_star (stdCoronaQuot J) (x.bddLift a))

theorem BusbyCycle.busbyFun_zero (x : BusbyCycle S J) : x.busbyFun 0 = 0 := by
  have h0 : x.busbyFun 0 = x.busbyFun 0 + x.busbyFun 0 :=
    (congrArg x.busbyFun (add_zero (0 : S)).symm).trans (x.busbyFun_add 0 0)
  exact left_eq_add.mp h0

/-- **The Busby map** `S → Q(J ⊗ 𝒦)` of a cycle, as a non-unital `⋆`-homomorphism. -/
def BusbyCycle.busbyₙ (x : BusbyCycle S J) : S →⋆ₙₐ[ℂ] StdCorona J where
  toFun := x.busbyFun
  map_smul' := x.busbyFun_smul
  map_zero' := x.busbyFun_zero
  map_add' := x.busbyFun_add
  map_mul' := x.busbyFun_mul
  map_star' := x.busbyFun_star

theorem BusbyCycle.busbyₙ_apply (x : BusbyCycle S J) (a : S) :
    x.busbyₙ a = stdCoronaMk (x.lift a) :=
  x.busbyFun_eq_stdCoronaMk a

theorem BusbyCycle.busbyₙ_apply_eq_quot (x : BusbyCycle S J) (a : S) :
    x.busbyₙ a = stdCoronaQuot J (x.bddLift a) := rfl

/-- Two cycles have the same Busby map iff their lifts agree modulo compacts. -/
theorem BusbyCycle.busbyₙ_eq_iff (x y : BusbyCycle S J) :
    x.busbyₙ = y.busbyₙ ↔ ∀ a : S, CompactEq J (x.lift a) (y.lift a) := by
  constructor
  · intro h a
    exact (stdCoronaQuot_eq_iff (x.bddLift a) (y.bddLift a)).mp
      (DFunLike.congr_fun h a)
  · intro h
    exact NonUnitalStarAlgHom.ext fun a =>
      (stdCoronaQuot_eq_iff (x.bddLift a) (y.bddLift a)).mpr (h a)

end NonUnital

section Unital

variable {S : Type} [CStarAlgebra S]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- A cycle is **unital** when the lift of `1` is the identity modulo compacts, i.e. the Busby
map is a unital `⋆`-homomorphism. -/
def BusbyCycle.IsUnital (x : BusbyCycle S J) : Prop :=
  CompactEq J (x.lift 1) (Adjointable.id (standardModule ℕ J))

theorem BusbyCycle.busbyFun_one (x : BusbyCycle S J) (hx : x.IsUnital) : x.busbyFun 1 = 1 :=
  ((stdCoronaQuot_eq_iff (x.bddLift 1) 1).mpr hx).trans (map_one (stdCoronaQuot J))

/-- **The Busby map** `S → Q(J ⊗ 𝒦)` of a unital cycle, as a unital `⋆`-homomorphism. -/
def BusbyCycle.busby (x : BusbyCycle S J) (hx : x.IsUnital) : S →⋆ₐ[ℂ] StdCorona J where
  toFun := x.busbyFun
  map_one' := x.busbyFun_one hx
  map_mul' := x.busbyFun_mul
  map_zero' := x.busbyFun_zero
  map_add' := x.busbyFun_add
  commutes' c := by
    show x.busbyFun (algebraMap ℂ S c) = algebraMap ℂ (StdCorona J) c
    exact ((congrArg x.busbyFun (Algebra.algebraMap_eq_smul_one (A := S) c)).trans
      ((x.busbyFun_smul c 1).trans (congrArg (fun q : StdCorona J => c • q)
        (x.busbyFun_one hx)))).trans
      (Algebra.algebraMap_eq_smul_one (A := StdCorona J) c).symm
  map_star' := x.busbyFun_star

theorem BusbyCycle.busby_apply (x : BusbyCycle S J) (hx : x.IsUnital) (a : S) :
    x.busby hx a = stdCoronaMk (x.lift a) :=
  x.busbyFun_eq_stdCoronaMk a

theorem BusbyCycle.busby_apply_eq_quot (x : BusbyCycle S J) (hx : x.IsUnital) (a : S) :
    x.busby hx a = stdCoronaQuot J (x.bddLift a) := rfl

/-- The unital Busby map forgets to the non-unital one. -/
theorem BusbyCycle.busby_apply_eq_busbyₙ (x : BusbyCycle S J) (hx : x.IsUnital) (a : S) :
    x.busby hx a = x.busbyₙ a := rfl

/-- Two unital cycles have the same Busby map iff their lifts agree modulo compacts. -/
theorem BusbyCycle.busby_eq_iff (x y : BusbyCycle S J) (hx : x.IsUnital) (hy : y.IsUnital) :
    x.busby hx = y.busby hy ↔ ∀ a : S, CompactEq J (x.lift a) (y.lift a) := by
  constructor
  · intro h a
    exact (stdCoronaQuot_eq_iff (x.bddLift a) (y.bddLift a)).mp
      (DFunLike.congr_fun h a)
  · intro h
    exact StarAlgHom.ext fun a =>
      (stdCoronaQuot_eq_iff (x.bddLift a) (y.bddLift a)).mpr (h a)

end Unital

end GroupApproximation.Full.TWWSchafhauser

end
