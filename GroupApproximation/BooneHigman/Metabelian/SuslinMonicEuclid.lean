import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import Mathlib.Algebra.Polynomial.Div
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin monic route, part 1: the Euclidean reduction on a monic entry

Lane `bh-met-41`.  The first step of Horrocks' argument (the local step of the monic route to
`SuslinOneVariableStatement`) is Euclidean division by a monic entry of a row: if the entry
`f_t` of row `t` of a matrix over `R[X]` is monic, then right multiplication by elementary
matrices `x_{t c}(-(f_c /ₘ f_t))` (for `c ≠ t`) replaces every other entry `f_c` of the row by
its remainder `f_c %ₘ f_t`, of degree `< deg f_t`, and leaves `f_t` in place.

The factors are the simultaneous right transvections `rightClearFactors` of
`PropertyTT/MatrixElimination.lean`, whose action is `mul_rightClearFactors_apply`; their product
is elementary by `RankNElimination.rightClearFactors_prod_mem`.  The coefficient ring `R` is an
arbitrary commutative ring (no locality, no Noetherianity).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open RankNElimination

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- **Euclidean reduction of a row modulo its entry at `t`.**  Right multiplication by an
elementary matrix replaces each entry `f_c` (`c ≠ t`) of row `t` by `f_c %ₘ f_t`. -/
theorem suslinMonic_exists_row_modByMonic (A : (Matrix ι ι (Polynomial R))ˣ) (t : ι) :
    ∃ F ∈ elementaryGroup ι (Polynomial R),
      ∀ c : ι, ((A * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) t c =
        if c = t then (A : Matrix ι ι (Polynomial R)) t t
        else (A : Matrix ι ι (Polynomial R)) t c %ₘ (A : Matrix ι ι (Polynomial R)) t t := by
  refine ⟨(rightClearFactors t (fun k ↦ -((A : Matrix ι ι (Polynomial R)) t k /ₘ
      (A : Matrix ι ι (Polynomial R)) t t)) (otherIndices t)).prod,
    rightClearFactors_prod_mem t _, fun c ↦ ?_⟩
  rw [Units.val_mul, mul_rightClearFactors_apply (A : Matrix ι ι (Polynomial R)) t _
    (otherIndices t) (otherIndices_nodup t)]
  by_cases hc : c = t
  · subst hc
    rw [if_neg (by simp), if_pos rfl]
  · rw [if_pos ((mem_otherIndices_values_iff t c).2 hc), if_neg hc]
    simp only [Polynomial.modByMonic_eq_sub_mul_div, mul_neg, sub_eq_add_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_exists_row_modByMonic

/-- **Degree reduction on a monic entry** (the Euclidean half of Horrocks' step): if the entry
of row `t` at `t` is monic, an elementary right factor keeps it and lowers the degree of every
other entry of the row below its degree. -/
theorem suslinMonic_exists_row_degree_lt [Nontrivial R] (A : (Matrix ι ι (Polynomial R))ˣ)
    (t : ι) (ht : ((A : Matrix ι ι (Polynomial R)) t t).Monic) :
    ∃ F ∈ elementaryGroup ι (Polynomial R),
      ((A * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) t t =
          (A : Matrix ι ι (Polynomial R)) t t ∧
        ∀ c : ι, c ≠ t →
          (((A * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) t c).degree <
            ((A : Matrix ι ι (Polynomial R)) t t).degree := by
  obtain ⟨F, hF, hrow⟩ := suslinMonic_exists_row_modByMonic A t
  refine ⟨F, hF, ?_, fun c hc ↦ ?_⟩
  · rw [hrow t, if_pos rfl]
  · rw [hrow c, if_neg hc]
    exact Polynomial.degree_modByMonic_lt _ ht

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinMonic_exists_row_degree_lt

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
