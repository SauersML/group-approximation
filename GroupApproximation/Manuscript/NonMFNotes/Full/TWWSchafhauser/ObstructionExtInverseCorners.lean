import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionSplitExtCorona
import GroupApproximation.Analysis.CStarDirectSumOperators
import GroupApproximation.Analysis.CStarUnitary

/-!
# Corners of operators on `H_J ⊕ H_J`

Lane `TWWSch3d2Inv`, work order `WO-TWWSch-3d2-Inv`, first file.

The inverse of a Busby cycle is the complement corner of a Stinespring dilation (Arveson,
Duke Math. J. 44 (1977), §4; Kasparov, J. Operator Theory 4 (1980), §7, Thm 2; Blackadar,
*K-theory for operator algebras*, 15.6–15.7). An operator `T` on `H_J ⊕ H_J` has four corners
`T₁₁, T₁₂, T₂₁, T₂₂`, and the dilation is read off them. This file sets up:

* `StdSum J = H_J ⊕ H_J` and `StdSumOp J`;
* `corner11`, `corner12`, `corner21`, `corner22` with their `toFun` values, all bounded when `T`
  is;
* `toFun_split'`: `T p = T (p₁, 0) + T (0, p₂)`, the four-corner decomposition pointwise;
* the calculus of `CompactEq` needed for the corner argument: `compactEq_of_toFun_eq`,
  `CompactEq.comp_left`, `CompactEq.comp_right`, `CompactEq.comp` (reflexivity, symmetry and
  transitivity are `compactEq_refl`, `compactEq_symm`, `compactEq_trans` of
  `ObstructionSplitExtCorona`).
-/

noncomputable section

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

universe w₁ w₂ w₃

section Corners

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

variable (J) in
/-- The direct sum `H_J ⊕ H_J` of two copies of the standard module. -/
abbrev StdSum : CStarModule.{0, 0} J :=
  HilbertModule.prod (standardModule ℕ J) (standardModule ℕ J)

variable (J) in
/-- The adjointable operators on `H_J ⊕ H_J`. -/
abbrev StdSumOp : Type :=
  Adjointable (StdSum J) (StdSum J)

/-- Composition preserves boundedness, for arbitrary modules over `J`. -/
theorem isBounded_comp {E : CStarModule.{0, w₁} J} {F : CStarModule.{0, w₂} J}
    {G : CStarModule.{0, w₃} J} {R : Adjointable F G} {T : Adjointable E F}
    (hR : R.IsBounded) (hT : T.IsBounded) : (Adjointable.comp R T).IsBounded := by
  obtain ⟨C, hC, hRb⟩ := hR
  obtain ⟨D, hD, hTb⟩ := hT
  exact ⟨C * D, mul_nonneg hC hD, hRb.comp hTb hC⟩

/-- The `(1,1)` corner `ξ ↦ (T (ξ, 0))₁`. -/
def corner11 (T : StdSumOp J) : StdOp J :=
  Adjointable.comp (Adjointable.fstProj (standardModule ℕ J) (standardModule ℕ J))
    (Adjointable.comp T (Adjointable.inl (standardModule ℕ J) (standardModule ℕ J)))

/-- The `(1,2)` corner `η ↦ (T (0, η))₁`. -/
def corner12 (T : StdSumOp J) : StdOp J :=
  Adjointable.comp (Adjointable.fstProj (standardModule ℕ J) (standardModule ℕ J))
    (Adjointable.comp T (Adjointable.inr (standardModule ℕ J) (standardModule ℕ J)))

/-- The `(2,1)` corner `ξ ↦ (T (ξ, 0))₂`. -/
def corner21 (T : StdSumOp J) : StdOp J :=
  Adjointable.comp (Adjointable.sndProj (standardModule ℕ J) (standardModule ℕ J))
    (Adjointable.comp T (Adjointable.inl (standardModule ℕ J) (standardModule ℕ J)))

/-- The `(2,2)` corner `η ↦ (T (0, η))₂`. -/
def corner22 (T : StdSumOp J) : StdOp J :=
  Adjointable.comp (Adjointable.sndProj (standardModule ℕ J) (standardModule ℕ J))
    (Adjointable.comp T (Adjointable.inr (standardModule ℕ J) (standardModule ℕ J)))

theorem corner11_toFun (T : StdSumOp J) (ξ : (standardModule ℕ J).carrier) :
    (corner11 T).toFun ξ = (T.toFun (ξ, 0)).1 := rfl

theorem corner12_toFun (T : StdSumOp J) (η : (standardModule ℕ J).carrier) :
    (corner12 T).toFun η = (T.toFun (0, η)).1 := rfl

theorem corner21_toFun (T : StdSumOp J) (ξ : (standardModule ℕ J).carrier) :
    (corner21 T).toFun ξ = (T.toFun (ξ, 0)).2 := rfl

theorem corner22_toFun (T : StdSumOp J) (η : (standardModule ℕ J).carrier) :
    (corner22 T).toFun η = (T.toFun (0, η)).2 := rfl

theorem isBounded_corner11 {T : StdSumOp J} (hT : T.IsBounded) : (corner11 T).IsBounded :=
  isBounded_comp Adjointable.isBounded_fstProj (isBounded_comp hT Adjointable.isBounded_inl)

theorem isBounded_corner12 {T : StdSumOp J} (hT : T.IsBounded) : (corner12 T).IsBounded :=
  isBounded_comp Adjointable.isBounded_fstProj (isBounded_comp hT Adjointable.isBounded_inr)

theorem isBounded_corner21 {T : StdSumOp J} (hT : T.IsBounded) : (corner21 T).IsBounded :=
  isBounded_comp Adjointable.isBounded_sndProj (isBounded_comp hT Adjointable.isBounded_inl)

theorem isBounded_corner22 {T : StdSumOp J} (hT : T.IsBounded) : (corner22 T).IsBounded :=
  isBounded_comp Adjointable.isBounded_sndProj (isBounded_comp hT Adjointable.isBounded_inr)

/-! ## Coordinates on `H_J ⊕ H_J` -/

theorem stdSum_fst_add (u v : (StdSum J).carrier) : (u + v).1 = u.1 + v.1 := rfl

theorem stdSum_snd_add (u v : (StdSum J).carrier) : (u + v).2 = u.2 + v.2 := rfl

theorem stdSum_snd_smul (c : ℂ) (u : (StdSum J).carrier) : (c • u).2 = c • u.2 := rfl

/-- **Four-corner decomposition**, pointwise: `T (ξ, η) = T (ξ, 0) + T (0, η)`. -/
theorem toFun_split (T : StdSumOp J) (ξ η : (standardModule ℕ J).carrier) :
    T.toFun (ξ, η) = T.toFun (ξ, 0) + T.toFun (0, η) := by
  have h : ((ξ, η) : (StdSum J).carrier) = (ξ, 0) + (0, η) := by
    show (ξ, η) = (ξ + 0, 0 + η)
    rw [add_zero, zero_add]
  rw [h, Adjointable.map_add]

theorem toFun_split' (T : StdSumOp J) (p : (StdSum J).carrier) :
    T.toFun p = T.toFun (p.1, 0) + T.toFun (0, p.2) :=
  toFun_split T p.1 p.2

/-! ## Compact perturbation -/

theorem CompactEq.isCompactOp {T T' : StdOp J} (h : CompactEq J T T') :
    Adjointable.IsCompactOp (Adjointable.sub T T') := h

/-- Operators with the same underlying map agree modulo compacts. -/
theorem compactEq_of_toFun_eq {T T' : StdOp J} (h : ∀ ξ, T.toFun ξ = T'.toFun ξ) :
    CompactEq J T T' := by
  show Adjointable.IsCompactOp (Adjointable.sub T T')
  refine Adjointable.IsCompactOp.congr
    (T := Adjointable.zero (standardModule ℕ J) (standardModule ℕ J)) (fun ξ => ?_)
    Adjointable.isCompactOp_zero
  show (0 : (standardModule ℕ J).carrier) = T.toFun ξ - T'.toFun ξ
  rw [h ξ, sub_self]

theorem CompactEq.comp_left {T T' R : StdOp J} (h : CompactEq J T T') (hR : R.IsBounded) :
    CompactEq J (Adjointable.comp R T) (Adjointable.comp R T') := by
  show Adjointable.IsCompactOp
    (Adjointable.sub (Adjointable.comp R T) (Adjointable.comp R T'))
  refine Adjointable.IsCompactOp.congr (fun ξ => ?_)
    (Adjointable.IsCompactOp.comp_left h.isCompactOp hR)
  show R.toFun (T.toFun ξ - T'.toFun ξ) = R.toFun (T.toFun ξ) - R.toFun (T'.toFun ξ)
  rw [Adjointable.map_sub]

theorem CompactEq.comp_right {T T' R : StdOp J} (h : CompactEq J T T') (hR : R.IsBounded) :
    CompactEq J (Adjointable.comp T R) (Adjointable.comp T' R) := by
  show Adjointable.IsCompactOp
    (Adjointable.sub (Adjointable.comp T R) (Adjointable.comp T' R))
  exact Adjointable.IsCompactOp.congr (T := Adjointable.comp (Adjointable.sub T T') R)
    (fun _ => rfl) (Adjointable.IsCompactOp.comp_right h.isCompactOp hR)

/-- Compact perturbations compose, for bounded factors. -/
theorem CompactEq.comp {T T' R R' : StdOp J} (hT : CompactEq J T T') (hR : CompactEq J R R')
    (hT' : T'.IsBounded) (hR0 : R.IsBounded) :
    CompactEq J (Adjointable.comp T R) (Adjointable.comp T' R') :=
  compactEq_trans (hT.comp_right hR0) (hR.comp_left hT')

end Corners

end GroupApproximation.Full.TWWSchafhauser

end
