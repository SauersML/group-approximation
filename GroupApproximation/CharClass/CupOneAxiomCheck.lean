import GroupApproximation.CharClass.CupOneComm

/-!
# Lane `sp-cupone`: axiom check and the `ZMod 2` instance

A leaf file, imported by nothing, kept out of the import closure on purpose so that
adding to it never forces a rebuild.  It records two things.

**1. The generic theorems apply to the `F₂` instance.**  `Hmod2` is reducibly
`Hmod (ZMod 2)`, so the signed statement is a statement about the mod-2 cohomology the
LIX answer is built on, and at `ZMod 2` its scalar is `1`.  The `F₂` file
`SteenrodCupOne.lean` is untouched and its `cup_comm` is unchanged.

**2. No axiom beyond the three standard ones** is used anywhere in the lane.
-/

open GroupApproximation.CharClass
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The signed statement, read at `K = ZMod 2`. -/
example {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = ((-1 : ZMod 2) ^ (p * q)) • cohCast (Nat.add_comm q p) (cup b a) :=
  cup_comm_signed a b

/-- The even-degree corollary, read at `K = ZMod 2`; the conclusion is literally the
statement of the `F₂` `SteenrodCupOne.cup_comm`. -/
example {X : TopCat.{0}} {p q : ℕ} (hp : Even p) (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = cohCast (Nat.add_comm q p) (cup b a) :=
  cup_comm_of_even_left hp a b

/-- **The signed cup-1 product IS the tree's cup-1 product at `ZMod 2`.**  Every sign is
`1` there, so `cochainCupOne` and `SteenrodCochain.cochainCupI 1` are the same cochain.
This is the cross-check that the signed development is a refinement of the `F₂` one and
not a different operation: `cochainCupOne_coboundary` therefore specialises to
`SteenrodCoboundary.cochainCupI_coboundary` at `i = 0`. -/
example {X : TopCat.{0}} (a b n : ℕ) (α : singularCochainGroup (ZMod 2) X a)
    (β : singularCochainGroup (ZMod 2) X b) :
    cochainCupOne a b n α β = cochainCupI 1 a b n α β := by
  apply cochain_ext
  intro σ
  rw [cochainCupOne_eval, cochainCupI_eval]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [cupOneSign_def, neg_one_pow_zmod2, one_mul]

#print axioms GroupApproximation.CharClass.cutExp_succAbove_cutU
#print axioms GroupApproximation.CharClass.cutExp_succAbove_cutV
#print axioms GroupApproximation.CharClass.faceVal_coboundary_signed
#print axioms GroupApproximation.CharClass.cut_insert_cancel_signed
#print axioms GroupApproximation.CharClass.cupOneSign_succAbove
#print axioms GroupApproximation.CharClass.cut_coboundary_master_signed
#print axioms GroupApproximation.CharClass.cochainCupOne_coboundary
#print axioms GroupApproximation.CharClass.cochainCupOne_coboundary_cocycle
#print axioms GroupApproximation.CharClass.CupOneLocal.cocycleClassK_add
#print axioms GroupApproximation.CharClass.CupOneLocal.cocycleClassK_smul
#print axioms GroupApproximation.CharClass.cup_comm_signed
#print axioms GroupApproximation.CharClass.cup_comm_of_even_left
#print axioms GroupApproximation.CharClass.cup_comm_of_even_right
