import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExt
import Mathlib.Algebra.Star.Subalgebra

/-!
# The `⋆`-algebra of adjointable operators

Lane `TWWSch3d4a`, work order `WO-TWWSch-3d4-1` (with `WO-TWWSch-3c-1`), first part.

The Busby-ring framework (`ObstructionSplit*.lean`) works with `⋆`-algebra homomorphisms
`E →⋆ₐ[ℂ] Q` between rings. The extension group `ExtGroup S J` (`ObstructionExt.lean`) works with
operators `StdOp J = 𝓛(H_J)` given as bundled `Adjointable` structures, without a ring structure.
This file puts the ring structure on `Adjointable E E` (Blackadar, *K-theory for operator
algebras*, §13; Lance, *Hilbert C⋆-modules*, Ch. 1):

* `adjointable_ext`: an adjointable operator is determined by its underlying map;
* `Ring`, `Module ℂ`, `Algebra ℂ`, `StarRing`, `StarModule ℂ` on `Adjointable E E`, with
  `T * U = T.comp U`, `star T = adjoint T`, pulled back along `adjToEnd` into `Module.End ℂ E`;
* `boundedAdj E`: the `⋆`-subalgebra of bounded operators, and `StdBdd J` for `E = H_J`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

universe v w

section Operators

variable {B : Type v} [NonUnitalCStarAlgebra B]
variable {E : CStarModule.{v, w} B}

/-- An adjointable operator is determined by its underlying map: the adjoint is unique. -/
theorem adjointable_ext {T U : Adjointable E E} (h : ∀ x, T.toFun x = U.toFun x) : T = U := by
  obtain ⟨f, g, p⟩ := T
  obtain ⟨f', g', p'⟩ := U
  have h1 : f = f' := funext h
  have h2 : g = g' :=
    funext (Adjointable.adj_eq_of_toFun_eq ⟨f, g, p⟩ ⟨f', g', p'⟩ h)
  subst h1
  subst h2
  rfl

/-- The underlying `ℂ`-linear endomorphism of an adjointable operator. -/
def adjToEnd (T : Adjointable E E) : Module.End ℂ E.carrier where
  toFun := T.toFun
  map_add' := T.map_add
  map_smul' := T.map_smul

theorem adjToEnd_injective : Function.Injective (adjToEnd (E := E)) :=
  fun _ _ h => adjointable_ext fun x => LinearMap.congr_fun h x

instance twwAdjZero : Zero (Adjointable E E) := ⟨Adjointable.zero E E⟩
instance twwAdjOne : One (Adjointable E E) := ⟨Adjointable.id E⟩
instance twwAdjAdd : Add (Adjointable E E) := ⟨Adjointable.add⟩
instance twwAdjMul : Mul (Adjointable E E) := ⟨Adjointable.comp⟩
instance twwAdjNeg : Neg (Adjointable E E) := ⟨Adjointable.neg⟩
instance twwAdjSub : Sub (Adjointable E E) := ⟨Adjointable.sub⟩
instance twwAdjSMul : SMul ℂ (Adjointable E E) := ⟨Adjointable.smul⟩
instance twwAdjNSMul : SMul ℕ (Adjointable E E) := ⟨fun n T => Adjointable.smul (n : ℂ) T⟩
instance twwAdjZSMul : SMul ℤ (Adjointable E E) := ⟨fun n T => Adjointable.smul (n : ℂ) T⟩
instance twwAdjPow : Pow (Adjointable E E) ℕ := ⟨fun T n => npowRec n T⟩
instance twwAdjNatCast : NatCast (Adjointable E E) :=
  ⟨fun n => Adjointable.smul (n : ℂ) (Adjointable.id E)⟩
instance twwAdjIntCast : IntCast (Adjointable E E) :=
  ⟨fun n => Adjointable.smul (n : ℂ) (Adjointable.id E)⟩

theorem zero_toFun (x : E.carrier) : (0 : Adjointable E E).toFun x = 0 := rfl
theorem one_toFun (x : E.carrier) : (1 : Adjointable E E).toFun x = x := rfl
theorem add_toFun' (T U : Adjointable E E) (x : E.carrier) :
    (T + U).toFun x = T.toFun x + U.toFun x := rfl
theorem mul_toFun (T U : Adjointable E E) (x : E.carrier) :
    (T * U).toFun x = T.toFun (U.toFun x) := rfl
theorem sub_toFun' (T U : Adjointable E E) (x : E.carrier) :
    (T - U).toFun x = T.toFun x - U.toFun x := rfl
theorem smul_toFun' (c : ℂ) (T : Adjointable E E) (x : E.carrier) :
    (c • T).toFun x = c • T.toFun x := rfl

theorem adjToEnd_zero : adjToEnd (0 : Adjointable E E) = 0 := LinearMap.ext fun _ => rfl

theorem adjToEnd_add (T U : Adjointable E E) : adjToEnd (T + U) = adjToEnd T + adjToEnd U :=
  LinearMap.ext fun _ => rfl

theorem adjToEnd_pow (T : Adjointable E E) (n : ℕ) : adjToEnd (T ^ n) = adjToEnd T ^ n := by
  induction n with
  | zero =>
    rw [pow_zero (adjToEnd T)]
    exact LinearMap.ext fun _ => rfl
  | succ n ih =>
    rw [pow_succ (adjToEnd T) n, ← ih]
    exact LinearMap.ext fun _ => rfl

/-- **`𝓛(E)` is a ring**, pulled back from `Module.End ℂ E` along the injective `adjToEnd`. -/
instance twwAdjRing : Ring (Adjointable E E) :=
  Function.Injective.ring adjToEnd adjToEnd_injective adjToEnd_zero
    (LinearMap.ext fun _ => rfl) adjToEnd_add (fun _ _ => LinearMap.ext fun _ => rfl)
    (fun T => LinearMap.ext fun x => Adjointable.neg_toFun T x)
    (fun T U => LinearMap.ext fun x => Adjointable.sub_toFun T U x)
    (fun n T => LinearMap.ext fun x => Nat.cast_smul_eq_nsmul ℂ n (T.toFun x))
    (fun n T => LinearMap.ext fun x => Int.cast_smul_eq_zsmul ℂ n (T.toFun x))
    adjToEnd_pow
    (fun n => LinearMap.ext fun x => Nat.cast_smul_eq_nsmul ℂ n x)
    (fun n => LinearMap.ext fun x => Int.cast_smul_eq_zsmul ℂ n x)

/-- `adjToEnd` as an additive homomorphism. -/
def adjToEndAddHom : Adjointable E E →+ Module.End ℂ E.carrier where
  toFun := adjToEnd
  map_zero' := adjToEnd_zero
  map_add' := adjToEnd_add

instance twwAdjModule : Module ℂ (Adjointable E E) :=
  Function.Injective.module ℂ adjToEndAddHom adjToEnd_injective
    (fun _ _ => LinearMap.ext fun _ => rfl)

instance twwAdjAlgebra : Algebra ℂ (Adjointable E E) :=
  Algebra.ofModule (fun _ _ _ => adjointable_ext fun _ => rfl)
    (fun c T U => adjointable_ext fun x => T.map_smul c (U.toFun x))

/-- **`𝓛(E)` is a `⋆`-ring** with `star T = T⋆`. All three identities hold by definition. -/
instance twwAdjStarRing : StarRing (Adjointable E E) where
  star := Adjointable.adjoint
  star_involutive _ := rfl
  star_mul _ _ := rfl
  star_add _ _ := rfl

theorem star_toFun (T : Adjointable E E) (x : E.carrier) : (star T).toFun x = T.adj x := rfl

instance twwAdjStarModule : StarModule ℂ (Adjointable E E) where
  star_smul _ _ := adjointable_ext fun _ => rfl

theorem algebraMap_toFun (c : ℂ) (x : E.carrier) :
    (algebraMap ℂ (Adjointable E E) c).toFun x = c • x := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-! ## Bounded operators -/

theorem isBounded_one : (1 : Adjointable E E).IsBounded :=
  ⟨1, zero_le_one, fun x => le_of_eq (one_mul (E.norm x)).symm⟩

theorem isBounded_zero : (0 : Adjointable E E).IsBounded :=
  ⟨0, le_rfl, fun x => le_of_eq (by
    show E.norm (0 : E.carrier) = 0 * E.norm x
    rw [E.norm_zero_vector, zero_mul])⟩

theorem isBounded_mul {T U : Adjointable E E} (hT : T.IsBounded) (hU : U.IsBounded) :
    (T * U).IsBounded := by
  obtain ⟨C, hC, hTC⟩ := hT
  obtain ⟨D, hD, hUD⟩ := hU
  exact ⟨C * D, mul_nonneg hC hD, hTC.comp hUD hC⟩

theorem isBounded_smul (c : ℂ) {T : Adjointable E E} (hT : T.IsBounded) : (c • T).IsBounded := by
  obtain ⟨C, hC, hTC⟩ := hT
  exact ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, hTC.smul c⟩

variable [PartialOrder B] [StarOrderedRing B]

theorem isBounded_add {T U : Adjointable E E} (hT : T.IsBounded) (hU : U.IsBounded) :
    (T + U).IsBounded := by
  obtain ⟨C, hC, hTC⟩ := hT
  obtain ⟨D, hD, hUD⟩ := hU
  exact ⟨C + D, add_nonneg hC hD, hTC.add hUD⟩

theorem isBounded_star {T : Adjointable E E} (hT : T.IsBounded) : (star T).IsBounded :=
  Adjointable.IsBounded.adjoint hT

variable (E) in
/-- **The bounded adjointable operators** form a `⋆`-subalgebra of `𝓛(E)`. -/
def boundedAdj : StarSubalgebra ℂ (Adjointable E E) where
  carrier := {T | T.IsBounded}
  mul_mem' := fun {a b} ha hb => by
    show (a * b).IsBounded
    exact isBounded_mul ha hb
  one_mem' := isBounded_one
  add_mem' := fun {a b} ha hb => by
    show (a + b).IsBounded
    exact isBounded_add ha hb
  zero_mem' := isBounded_zero
  algebraMap_mem' := fun c => by
    show (algebraMap ℂ (Adjointable E E) c).IsBounded
    rw [Algebra.algebraMap_eq_smul_one]
    exact isBounded_smul c isBounded_one
  star_mem' := fun {a} ha => by
    show (star a).IsBounded
    exact isBounded_star ha

theorem mem_boundedAdj {T : Adjointable E E} : T ∈ boundedAdj E ↔ T.IsBounded := Iff.rfl

end Operators

section Std

variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- The bounded operators on `H_J = standardModule ℕ J`, a unital `⋆`-algebra over `ℂ`. -/
abbrev StdBdd : Type := ↥(boundedAdj (standardModule ℕ J))

end Std

end GroupApproximation.Full.TWWSchafhauser
