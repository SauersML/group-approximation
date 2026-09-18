import GroupApproximation.BooneHigman.Metabelian.SuslinZHalfEndpoint
import GroupApproximation.BooneHigman.Metabelian.SuslinNormalOrthogonal
import GroupApproximation.Leavitt.ElementaryStabilization
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# Orthogonal rank-one transvections in `SL₂` are stably elementary

Lane `bh-met-93u`.  Let `R` be a commutative ring and `v, w ∈ R²` with `wᵀ v = 0`.  The
`2 × 2` matrix `T = 1 + v wᵀ` is invertible, with inverse `1 - v wᵀ`.  Its stabilization
`diag(T, 1)` is ELEMENTARY in `E₃(R)` (`suslinZLocal_stab_mem_of_mem_TSet`).  Indeed
`diag(T, 1) = 1 + x yᵀ` with `x = (v, 0)` and `y = (w, 0)`.  Here `yᵀ x = 0` and `y` vanishes at
the third coordinate, so the corpus lemma `suslinNormal_inE_of_dot_zero` applies.  That lemma
is proved by the commutator `[1 + x e₃ᵀ, 1 + e₃ yᵀ] = 1 + x yᵀ`.

**Cohn's matrices.**  For `a, b ∈ R` the matrix `[[1 + ab, a²], [-b², 1 - ab]]` is
`1 + (a, -b)(b, a)ᵀ` and `(b, a)·(a, -b) = 0` (`suslinZLocal_cohn_mem_TSet`).  So Cohn's
matrices lie in `suslinZLocal_TSet R`.  In particular the lane-`bh-met-93p` counterexample
`a = 2sX`, `b = 4X` to one-sided elementary monic witnesses is stably elementary outright.

No literature input is used.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- The orthogonal rank-one transvections `1 + v wᵀ` with `wᵀ v = 0` in `GL₂(R)`. -/
def suslinZLocal_TSet (R : Type*) [CommRing R] : Set (Matrix (Fin 2) (Fin 2) R)ˣ :=
  {g | ∃ v w : Fin 2 → R, w 0 * v 0 + w 1 * v 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) R) = 1 + Matrix.vecMulVec v w}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_TSet

/-- **An orthogonal rank-one transvection is stably elementary.**  If `g = 1 + v wᵀ` with
`wᵀ v = 0`, then `diag(g, 1) ∈ E₃(R)`. -/
theorem suslinZLocal_stab_mem_of_mem_TSet {R : Type*} [CommRing R]
    {g : (Matrix (Fin 2) (Fin 2) R)ˣ} (hg : g ∈ suslinZLocal_TSet R) :
    stabilizeUnit (R := R) (κ := Unit) g ∈ elementaryGroup (Fin 2 ⊕ Unit) R := by
  obtain ⟨v, w, hwv, hgv⟩ := hg
  have hyk : (Sum.elim w 0 : Fin 2 ⊕ Unit → R) (Sum.inr ()) = 0 := rfl
  have hyx : (Sum.elim w 0 : Fin 2 ⊕ Unit → R) ⬝ᵥ (Sum.elim v 0 : Fin 2 ⊕ Unit → R) = 0 := by
    simp only [dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    exact hwv
  obtain ⟨u, hu, hval⟩ := suslinNormal_inE_of_dot_zero (x := Sum.elim v 0) (y := Sum.elim w 0)
    (k := Sum.inr ()) hyk hyx
  have heq : u = stabilizeUnit (R := R) (κ := Unit) g := by
    refine Units.ext ?_
    rw [hval, stabilizeUnit_val, hgv]
    refine Matrix.ext fun i j ↦ ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.one_apply, Matrix.vecMulVec_apply]
  rw [← heq]
  exact hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_stab_mem_of_mem_TSet

/-- **Cohn's matrices are orthogonal rank-one transvections.**  If
`g = [[1 + ab, a²], [-b², 1 - ab]]` then `g = 1 + (a, -b)(b, a)ᵀ` with `(b, a)·(a, -b) = 0`. -/
theorem suslinZLocal_cohn_mem_TSet {R : Type*} [CommRing R] (a b : R)
    (g : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (hg : (g : Matrix (Fin 2) (Fin 2) R) = !![1 + a * b, a ^ 2; -b ^ 2, 1 - a * b]) :
    g ∈ suslinZLocal_TSet R := by
  refine ⟨![a, -b], ![b, a], ?_, ?_⟩
  · show b * a + a * -b = 0
    ring
  · rw [hg]
    refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, Matrix.one_apply, sq] <;> ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_cohn_mem_TSet

/-- **Cohn's matrices are stably elementary** over every commutative ring. -/
theorem suslinZLocal_cohn_stab_mem {R : Type*} [CommRing R] (a b : R)
    (g : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (hg : (g : Matrix (Fin 2) (Fin 2) R) = !![1 + a * b, a ^ 2; -b ^ 2, 1 - a * b]) :
    stabilizeUnit (R := R) (κ := Unit) g ∈ elementaryGroup (Fin 2 ⊕ Unit) R :=
  suslinZLocal_stab_mem_of_mem_TSet (suslinZLocal_cohn_mem_TSet a b g hg)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinZLocal_cohn_stab_mem

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
