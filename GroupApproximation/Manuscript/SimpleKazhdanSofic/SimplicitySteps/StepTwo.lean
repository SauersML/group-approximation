import GroupApproximation.Manuscript.SimpleKazhdanSofic.SimplicitySteps.Setup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralSimplicityStatement
import Mathlib.SetTheory.Cardinal.Finite
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity, Step 2: the definitions over the tower

`simple_kazhdan_sofic_group.tex`, subsection "Simplicity", Step 2, tex l.272–273:

> Put $d=3|B_w|$. (l.272) For $a,b\in B_w$ put $\epsilon_{ab}=e_{aV}u_{ab^{-1}}$
> (Figure~\ref{fig:models}(b)). (l.272–273)

The printed `3` is the matrix size `n = 3` of the manuscript; for general `n` the tower dimension is
`d = n |B_w|` (`towerDim`), and it is at least `3` for `n ≥ 3` because `e ∈ B_w`.
`ε_ab = e_{aV} u_{ab⁻¹}` is `epsilonEntry`, in the crossed product
`R = ClopenGroupCrossedProduct Λ Z (ZMod 2)`; it agrees with the general `SimpleKazhdanSofic.epsilon`
for the covariant pair `(coeff, unitHom)` of this crossed product (`epsilonEntry_eq_epsilon`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SimplicitySteps

open scoped Pointwise

variable {Λ Z : Type*} [Group Λ] [TopologicalSpace Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z]

/-- **tex l.272**: the tower dimension `d = n |B_w|` (printed with `n = 3`). -/
noncomputable def towerDim (n : ℕ) (T : Set Λ) (w : ℕ) : ℕ :=
  n * Nat.card ↥(wordBall T w)

/-- The tower dimension is at least `3` when `n ≥ 3`, since `B_w` is finite and contains `e`. -/
theorem three_le_towerDim {T : Set Λ} (hT : T.Finite) (w : ℕ) {n : ℕ} (hn : 3 ≤ n) :
    3 ≤ towerDim n T w := by
  haveI : Finite ↥(wordBall T w) := (finite_wordBall hT w).to_subtype
  haveI : Nonempty ↥(wordBall T w) := ⟨⟨1, one_mem_wordBall T w⟩⟩
  have hpos : 0 < Nat.card ↥(wordBall T w) := Nat.card_pos
  unfold towerDim
  exact hn.trans (Nat.le_mul_of_pos_right n hpos)

/-- **tex l.272–273**: `ε_ab = e_{aV} u_{ab⁻¹}` in `LC(Z, F_2) ⋊ Λ`. -/
noncomputable def epsilonEntry {V : Set Z} (hV : IsClopen V) (a b : Λ) :
    ClopenGroupCrossedProduct Λ Z (ZMod 2) :=
  ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2) (LocallyConstant.charFn (ZMod 2) (isClopen_smul a hV)) *
    (ClopenGroupCrossedProduct.unit Λ Z (ZMod 2) (a * b⁻¹) : ClopenGroupCrossedProduct Λ Z (ZMod 2))

/-- `ε_ab` is the general `epsilon` for the covariant pair `(coeff, unitHom)` of the crossed
product. -/
theorem epsilonEntry_eq_epsilon {V : Set Z} (hV : IsClopen V) (a b : Λ) :
    epsilonEntry hV a b =
      epsilon (ClopenGroupCrossedProduct.coeff Λ Z (ZMod 2))
        (ClopenGroupCrossedProduct.unitHom Λ Z (ZMod 2)) hV a b :=
  rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.three_le_towerDim
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimplicitySteps.epsilonEntry_eq_epsilon

end SimplicitySteps
end SimpleKazhdanSofic
end GroupApproximation
