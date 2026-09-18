import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtRing
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitSum
import Mathlib.RingTheory.Congruence.Basic

/-!
# The corona algebra `Q(J ⊗ 𝒦)` and its Cuntz pair

Lane `TWWSch3d4a`, work order `WO-TWWSch-3d4-1` (with `WO-TWWSch-3c-1`), second part.

The corona algebra of `J ⊗ 𝒦` is `𝓛(H_J)/𝒦(H_J)` with `H_J = standardModule ℕ J` (Kasparov,
J. Operator Theory 4 (1980), §1; Blackadar, *K-theory for operator algebras*, §12.1, §15.4). The
Busby-ring framework (`ObstructionSplit*.lean`) needs it as a ring with a `⋆`-homomorphism from a
`⋆`-algebra of lifts. We take the bounded adjointable operators `StdBdd J` and divide by the ring
congruence "the difference is compact":

* `compactEq_refl`, `compactEq_symm`, `compactEq_trans`, `compactEq_add`, `compactEq_mul`,
  `compactEq_star`: `CompactEq J` is a `⋆`-congruence on bounded operators;
* `StdCorona J`: the quotient, a unital `ℂ`-algebra with a `⋆`-ring structure;
* `stdCoronaQuot J : StdBdd J →⋆ₐ[ℂ] StdCorona J` with `stdCoronaQuot_eq_iff`;
* `stdCoronaMk`: the quotient map on all of `StdOp J`, with `stdCoronaMk_eq_iff` on bounded
  operators;
* `stdCuntzPairBdd J`: the even/odd isometries `n ↦ 2n`, `n ↦ 2n+1` of `H_J`, built from the
  unitary `natSumMerge J : H_J ⊕ H_J → H_J`, as a `BusbyCuntzPair (StdBdd J)`;
* `stdCuntzPair J = (stdCuntzPairBdd J).map (stdCoronaQuot J)`: its image in the corona.

A Busby map lands in `StdCorona J`, the corona of the ideal, and not in an ultrapower: the latter
has no Cuntz pair under a faithful trace (the flaw found in `ExtensionFiniteTrace`).
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

universe v w w' w''

section Bounded

variable {B : Type v} [NonUnitalCStarAlgebra B]
variable {E : CStarModule.{v, w} B} {F : CStarModule.{v, w'} B} {G : CStarModule.{v, w''} B}

theorem isBounded_comp_of {S : Adjointable F G} {T : Adjointable E F} (hS : S.IsBounded)
    (hT : T.IsBounded) : (S.comp T).IsBounded := by
  obtain ⟨C, hC, hSC⟩ := hS
  obtain ⟨D, hD, hTD⟩ := hT
  exact ⟨C * D, mul_nonneg hC hD, hSC.comp hTD hC⟩

end Bounded

section Congruence

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

theorem compactEq_refl (T : StdOp J) : CompactEq J T T :=
  Adjointable.IsCompactOp.congr (T := Adjointable.zero (standardModule ℕ J) (standardModule ℕ J))
    (T' := Adjointable.sub T T) (fun x => (sub_self (T.toFun x)).symm)
    Adjointable.isCompactOp_zero

theorem compactEq_symm {T U : StdOp J} (h : CompactEq J T U) : CompactEq J U T :=
  Adjointable.IsCompactOp.congr (T := Adjointable.smul (-1) (Adjointable.sub T U))
    (T' := Adjointable.sub U T)
    (fun x => by
      show (-1 : ℂ) • (T.toFun x - U.toFun x) = U.toFun x - T.toFun x
      rw [neg_one_smul ℂ, neg_sub])
    (Adjointable.IsCompactOp.smul (T := Adjointable.sub T U) h (-1))

theorem compactEq_trans {T U V : StdOp J} (h1 : CompactEq J T U) (h2 : CompactEq J U V) :
    CompactEq J T V :=
  Adjointable.IsCompactOp.congr
    (T := Adjointable.add (Adjointable.sub T U) (Adjointable.sub U V))
    (T' := Adjointable.sub T V)
    (fun x => sub_add_sub_cancel (T.toFun x) (U.toFun x) (V.toFun x))
    (Adjointable.IsCompactOp.add (T := Adjointable.sub T U) (S := Adjointable.sub U V) h1 h2)

theorem compactEq_add {T T' U U' : StdOp J} (h1 : CompactEq J T T') (h2 : CompactEq J U U') :
    CompactEq J (T + U) (T' + U') :=
  Adjointable.IsCompactOp.congr
    (T := Adjointable.add (Adjointable.sub T T') (Adjointable.sub U U'))
    (T' := Adjointable.sub (T + U) (T' + U'))
    (fun x => by
      show T.toFun x - T'.toFun x + (U.toFun x - U'.toFun x)
        = T.toFun x + U.toFun x - (T'.toFun x + U'.toFun x)
      rw [sub_add_sub_comm])
    (Adjointable.IsCompactOp.add (T := Adjointable.sub T T') (S := Adjointable.sub U U') h1 h2)

/-- `TU - T'U' = (T - T')U + T'(U - U')`: compact perturbations multiply, for bounded factors. -/
theorem compactEq_mul {T T' U U' : StdOp J} (hT' : T'.IsBounded) (hU : U.IsBounded)
    (h1 : CompactEq J T T') (h2 : CompactEq J U U') : CompactEq J (T * U) (T' * U') :=
  Adjointable.IsCompactOp.congr
    (T := Adjointable.add ((Adjointable.sub T T').comp U) (T'.comp (Adjointable.sub U U')))
    (T' := Adjointable.sub (T * U) (T' * U'))
    (fun x => by
      show T.toFun (U.toFun x) - T'.toFun (U.toFun x) + T'.toFun (U.toFun x - U'.toFun x)
        = T.toFun (U.toFun x) - T'.toFun (U'.toFun x)
      rw [Adjointable.map_sub T' (U.toFun x) (U'.toFun x)]
      exact sub_add_sub_cancel _ _ _)
    (Adjointable.IsCompactOp.add
      (Adjointable.IsCompactOp.comp_right (T := Adjointable.sub T T') h1 hU)
      (Adjointable.IsCompactOp.comp_left (T := Adjointable.sub U U') h2 hT'))

theorem compactEq_star {T U : StdOp J} (h : CompactEq J T U) : CompactEq J (star T) (star U) :=
  Adjointable.IsCompactOp.adjoint (T := Adjointable.sub T U) h

variable (J) in
/-- **Compact perturbation** as a ring congruence on the bounded operators on `H_J`. -/
def stdCompactCon : RingCon (StdBdd J) where
  r T U := CompactEq J T.1 U.1
  iseqv := ⟨fun T => compactEq_refl T.1, fun h => compactEq_symm h,
    fun h1 h2 => compactEq_trans h1 h2⟩
  mul' := fun {_w x y _z} h1 h2 =>
    compactEq_mul (mem_boundedAdj.mp x.2) (mem_boundedAdj.mp y.2) h1 h2
  add' := fun h1 h2 => compactEq_add h1 h2

end Congruence

section Corona

variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **The corona algebra** `Q(J ⊗ 𝒦) = 𝓑(H_J)/𝒦(H_J)`, a unital `ℂ`-algebra. -/
abbrev StdCorona : Type := (stdCompactCon J).Quotient

instance twwStdCoronaStar : Star (StdCorona J) :=
  ⟨Quotient.map' (s₁ := (stdCompactCon J).toSetoid) (s₂ := (stdCompactCon J).toSetoid)
    (star : StdBdd J → StdBdd J) fun T U h =>
    compactEq_star (T := T.1) (U := U.1) h⟩

instance twwStdCoronaStarRing : StarRing (StdCorona J) where
  star_involutive x := Quotient.inductionOn' x fun T =>
    congrArg (Quotient.mk'' : StdBdd J → StdCorona J) (star_star T)
  star_mul x y := Quotient.inductionOn₂' x y fun T U =>
    congrArg (Quotient.mk'' : StdBdd J → StdCorona J) (star_mul T U)
  star_add x y := Quotient.inductionOn₂' x y fun T U =>
    congrArg (Quotient.mk'' : StdBdd J → StdCorona J) (star_add T U)

/-- **The quotient `⋆`-homomorphism** `𝓑(H_J) → Q(J ⊗ 𝒦)`. -/
def stdCoronaQuot : StdBdd J →⋆ₐ[ℂ] StdCorona J :=
  { (stdCompactCon J).mkₐ ℂ with map_star' := fun _ => rfl }

variable {J}

theorem stdCoronaQuot_apply (T : StdBdd J) :
    stdCoronaQuot J T = (Quotient.mk'' T : StdCorona J) := rfl

theorem stdCoronaQuot_eq_iff (T U : StdBdd J) :
    stdCoronaQuot J T = stdCoronaQuot J U ↔ CompactEq J T.1 U.1 :=
  ⟨fun h => (RingCon.eq (stdCompactCon J) (a := T) (b := U)).mp h,
    fun h => (RingCon.eq (stdCompactCon J) (a := T) (b := U)).mpr h⟩

/-- The class of an operator in the corona; unbounded operators are sent to `0`. -/
def stdCoronaMk (T : StdOp J) : StdCorona J :=
  @dite _ T.IsBounded (Classical.propDecidable _)
    (fun h => stdCoronaQuot J ⟨T, mem_boundedAdj.mpr h⟩) fun _ => 0

theorem stdCoronaMk_of_isBounded {T : StdOp J} (h : T.IsBounded) :
    stdCoronaMk T = stdCoronaQuot J ⟨T, mem_boundedAdj.mpr h⟩ :=
  dif_pos h

theorem stdCoronaMk_coe (T : StdBdd J) : stdCoronaMk T.1 = stdCoronaQuot J T :=
  stdCoronaMk_of_isBounded (mem_boundedAdj.mp T.2)

theorem stdCoronaMk_eq_iff {T T' : StdOp J} (hT : T.IsBounded) (hT' : T'.IsBounded) :
    stdCoronaMk T = stdCoronaMk T' ↔ CompactEq J T T' := by
  rw [stdCoronaMk_of_isBounded hT, stdCoronaMk_of_isBounded hT']
  exact stdCoronaQuot_eq_iff _ _

end Corona

section Cuntz

variable (J : Type) [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **The even/odd isometries of `H_J`** as a Cuntz pair of bounded operators:
`s₁ = V ∘ inl`, `s₂ = V ∘ inr` with `V : H_J ⊕ H_J → H_J` the unitary merging the even and odd
coordinates (`Adjointable.natSumMerge`). -/
def stdCuntzPairBdd : BusbyCuntzPair (StdBdd J) where
  s₁ := ⟨(Adjointable.natSumMerge J).comp
      (Adjointable.inl (standardModule ℕ J) (standardModule ℕ J)),
    mem_boundedAdj.mpr (isBounded_comp_of (Adjointable.isUnitaryAdj_natSumMerge J).isBounded
      Adjointable.isBounded_inl)⟩
  s₂ := ⟨(Adjointable.natSumMerge J).comp
      (Adjointable.inr (standardModule ℕ J) (standardModule ℕ J)),
    mem_boundedAdj.mpr (isBounded_comp_of (Adjointable.isUnitaryAdj_natSumMerge J).isBounded
      Adjointable.isBounded_inr)⟩
  star_mul_self₁ := Subtype.ext (adjointable_ext fun x =>
    congrArg (Adjointable.inl (standardModule ℕ J) (standardModule ℕ J)).adj
      ((Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun
        ((Adjointable.inl (standardModule ℕ J) (standardModule ℕ J)).toFun x)))
  star_mul_self₂ := Subtype.ext (adjointable_ext fun x =>
    congrArg (Adjointable.inr (standardModule ℕ J) (standardModule ℕ J)).adj
      ((Adjointable.isUnitaryAdj_natSumMerge J).adj_toFun
        ((Adjointable.inr (standardModule ℕ J) (standardModule ℕ J)).toFun x)))
  sum_eq_one := Subtype.ext (adjointable_ext fun y => by
    have hp : (((Adjointable.natSumMerge J).adj y).1, (0 : (standardModule ℕ J).carrier))
        + ((0 : (standardModule ℕ J).carrier), ((Adjointable.natSumMerge J).adj y).2)
        = (Adjointable.natSumMerge J).adj y :=
      Prod.ext (add_zero _) (zero_add _)
    exact (Adjointable.map_add (Adjointable.natSumMerge J)
        (((Adjointable.natSumMerge J).adj y).1, 0)
        (0, ((Adjointable.natSumMerge J).adj y).2)).symm.trans
      ((congrArg (Adjointable.natSumMerge J).toFun hp).trans
        ((Adjointable.isUnitaryAdj_natSumMerge J).toFun_adj y)))

/-- **The Cuntz pair of the corona** `Q(J ⊗ 𝒦)`: the image of the even/odd isometries. -/
def stdCuntzPair : BusbyCuntzPair (StdCorona J) :=
  (stdCuntzPairBdd J).map (stdCoronaQuot J)

theorem stdCuntzPair_s₁ : (stdCuntzPair J).s₁ = stdCoronaQuot J (stdCuntzPairBdd J).s₁ := rfl

theorem stdCuntzPair_s₂ : (stdCuntzPair J).s₂ = stdCoronaQuot J (stdCuntzPairBdd J).s₂ := rfl

end Cuntz

end GroupApproximation.Full.TWWSchafhauser

end
