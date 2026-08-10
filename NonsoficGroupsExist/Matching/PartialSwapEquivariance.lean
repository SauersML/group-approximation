import NonsoficGroupsExist.Matching.PartialBijectionSwap
import NonsoficGroupsExist.Matching.PartialEquivarianceBoundary

/-!
# Equivariance of the swap encoding

The commutation defects of the involution encoding of a partial bijection
inject into the forward and backward partial-equivariance defects.  Missing
points which stay inside the missing set do not create a swap commutator;
this is why the comparison is an inequality rather than an equality.
-/

namespace NonsoficGroupsExist
namespace FinitePartialBijection

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {Y Z : FiniteModel}

/-- The componentwise label action on the disjoint union. -/
def sumAction (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (s : L) : Equiv.Perm (sumModel Y Z) :=
  Equiv.sumCongr (actY s) (actZ s)

/-- Labelled commutation failures of the swap involution. -/
noncomputable def swapEquivarianceDefect
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    Finset (L × (Y ⊕ Z)) := by
  classical
  exact Finset.univ.filter fun p ↦
    b.swapPerm (sumAction actY actZ p.1 p.2) ≠
      sumAction actY actZ p.1 (b.swapPerm p.2)

omit [DecidableEq L] in
@[simp] theorem mem_swapEquivarianceDefect
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (p : L × (Y ⊕ Z)) :
    p ∈ b.swapEquivarianceDefect actY actZ ↔
      b.swapPerm (sumAction actY actZ p.1 p.2) ≠
        sumAction actY actZ p.1 (b.swapPerm p.2) := by
  classical
  simp [swapEquivarianceDefect]

omit [DecidableEq L] in
/-- A left-layer swap commutator is a forward partial-equivariance defect. -/
theorem left_mem_equivarianceDefect_of_swap
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (s : L) (y : Y)
    (h : (s, Sum.inl y) ∈ b.swapEquivarianceDefect actY actZ) :
    (s, y) ∈ b.equivarianceDefect actY actZ := by
  classical
  rw [mem_swapEquivarianceDefect] at h
  rw [mem_equivarianceDefect]
  intro hy hsy heq
  simp only [sumAction] at h
  rw [swapPerm_inl_of_mem b y hy] at h
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] at h
  rw [swapPerm_inl_of_mem b (actY s y) hsy] at h
  exact h (congrArg Sum.inr heq)

omit [DecidableEq L] in
/-- A right-layer swap commutator is a backward partial-equivariance defect. -/
theorem right_mem_equivarianceDefect_of_swap
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (s : L) (z : Z)
    (h : (s, Sum.inr z) ∈ b.swapEquivarianceDefect actY actZ) :
    (s, z) ∈ b.symm.equivarianceDefect actZ actY := by
  classical
  rw [mem_swapEquivarianceDefect] at h
  rw [mem_equivarianceDefect]
  intro hz hsz heq
  simp only [sumAction] at h
  rw [swapPerm_inr_of_mem b z hz] at h
  simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr] at h
  rw [swapPerm_inr_of_mem b (actZ s z) hsz] at h
  exact h (congrArg Sum.inl heq)

omit [DecidableEq L] in
/-- Every swap commutator is charged injectively to a forward defect on the
left layer or a backward defect on the right layer. -/
theorem card_swapEquivarianceDefect_le
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    (b.swapEquivarianceDefect actY actZ).card ≤
      (b.equivarianceDefect actY actZ).card +
        (b.symm.equivarianceDefect actZ actY).card := by
  classical
  let charge :
      {p // p ∈ b.swapEquivarianceDefect actY actZ} →
        {p // p ∈ b.equivarianceDefect actY actZ} ⊕
          {p // p ∈ b.symm.equivarianceDefect actZ actY}
    | ⟨(s, Sum.inl y), h⟩ =>
        Sum.inl ⟨(s, y), left_mem_equivarianceDefect_of_swap
          b actY actZ s y h⟩
    | ⟨(s, Sum.inr z), h⟩ =>
        Sum.inr ⟨(s, z), right_mem_equivarianceDefect_of_swap
          b actY actZ s z h⟩
  let forget :
      {p // p ∈ b.equivarianceDefect actY actZ} ⊕
          {p // p ∈ b.symm.equivarianceDefect actZ actY} →
        L × (Y ⊕ Z)
    | Sum.inl p => (p.1.1, Sum.inl p.1.2)
    | Sum.inr p => (p.1.1, Sum.inr p.1.2)
  have hforget (p : {p // p ∈ b.swapEquivarianceDefect actY actZ}) :
      forget (charge p) = p.1 := by
    rcases p with ⟨⟨s, y | z⟩, hp⟩ <;> rfl
  have hcharge : Function.Injective charge := by
    intro p q hpq
    apply Subtype.ext
    rw [← hforget p, hpq, hforget q]
  have hcard := Fintype.card_le_of_injective charge hcharge
  simpa only [Fintype.card_coe, Fintype.card_sum] using hcard

end FinitePartialBijection
end NonsoficGroupsExist
