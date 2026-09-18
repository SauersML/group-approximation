import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.KMSPresentation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Finite indexing of the Kharlampovich generators

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, in the
form of the coding step for the Kharlampovich group `KMS.KhGroup M`.

The generator type `KMS.KhGen K N` is finite: it is in bijection with
`(Fin (N+1) × Finset (Fin (K+1))) ⊕ Fin (K+1) ⊕ Fin K ⊕ Fin K ⊕ Fin K ⊕ Fin K`.
We fix a bijection `genEquiv K N : KhGen K N ≃ Fin (genIndexCount K N + 1)`,
which is the letter numbering used by the presentation code of `KhGroup M`.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

variable {K N : ℕ}

/-- The sum type in bijection with `KhGen K N`. -/
abbrev KhGenSum (K N : ℕ) : Type :=
  (Fin (N + 1) × Finset (Fin (K + 1))) ⊕ (Fin (K + 1) ⊕ (Fin K ⊕ (Fin K ⊕ (Fin K ⊕ Fin K))))

/-- The generators of `G(M)` as elements of `KhGenSum K N`. -/
def khGenToSum : KhGen K N → KhGenSum K N
  | .x j S => .inl (j, S)
  | .bigA i => .inr (.inl i)
  | .a n => .inr (.inr (.inl n))
  | .a' n => .inr (.inr (.inr (.inl n)))
  | .ta n => .inr (.inr (.inr (.inr (.inl n))))
  | .ta' n => .inr (.inr (.inr (.inr (.inr n))))

/-- The inverse of `khGenToSum`. -/
def khGenOfSum : KhGenSum K N → KhGen K N
  | .inl (j, S) => .x j S
  | .inr (.inl i) => .bigA i
  | .inr (.inr (.inl n)) => .a n
  | .inr (.inr (.inr (.inl n))) => .a' n
  | .inr (.inr (.inr (.inr (.inl n)))) => .ta n
  | .inr (.inr (.inr (.inr (.inr n)))) => .ta' n

theorem khGenOfSum_toSum (g : KhGen K N) : khGenOfSum (khGenToSum g) = g :=
  match g with
  | .x _ _ => rfl
  | .bigA _ => rfl
  | .a _ => rfl
  | .a' _ => rfl
  | .ta _ => rfl
  | .ta' _ => rfl

theorem khGenToSum_ofSum (s : KhGenSum K N) : khGenToSum (khGenOfSum s) = s :=
  match s with
  | .inl (_, _) => rfl
  | .inr (.inl _) => rfl
  | .inr (.inr (.inl _)) => rfl
  | .inr (.inr (.inr (.inl _))) => rfl
  | .inr (.inr (.inr (.inr (.inl _)))) => rfl
  | .inr (.inr (.inr (.inr (.inr _)))) => rfl

/-- The bijection `KhGen K N ≃ KhGenSum K N`. -/
def khGenEquivSum (K N : ℕ) : KhGen K N ≃ KhGenSum K N where
  toFun := khGenToSum
  invFun := khGenOfSum
  left_inv := khGenOfSum_toSum
  right_inv := khGenToSum_ofSum

instance instFintypeKhGen : Fintype (KhGen K N) :=
  Fintype.ofEquiv (KhGenSum K N) (khGenEquivSum K N).symm

instance instNonemptyKhGen : Nonempty (KhGen K N) :=
  ⟨KhGen.x 0 ∅⟩

/-- The largest letter index of the presentation code of `G(M)`. -/
noncomputable def genIndexCount (K N : ℕ) : ℕ :=
  Fintype.card (KhGen K N) - 1

theorem card_khGen_eq (K N : ℕ) : Fintype.card (KhGen K N) = genIndexCount K N + 1 := by
  have h : 0 < Fintype.card (KhGen K N) := Fintype.card_pos
  unfold genIndexCount
  omega

/-- The letter numbering `KhGen K N ≃ Fin (genIndexCount K N + 1)`. -/
noncomputable def genEquiv (K N : ℕ) : KhGen K N ≃ Fin (genIndexCount K N + 1) :=
  Fintype.equivFinOfCardEq (card_khGen_eq K N)

end KMS

end GroupApproximation.Full.Kharlampovich
