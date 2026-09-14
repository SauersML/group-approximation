import GroupApproximation.Pestov91.SimpleModCentre
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# The exponent bound and the commutator `k = [g, h]`

`simple_kazhdan_sofic_group.tex` at e80dcf20a, subsection "Simplicity" (tex l.180–181, l.213):

> Let $1\ne N\trianglelefteq G$ and $1\ne g\in N$, and let $w\ge0$ bound the absolute values of
> the exponents in the entries of $g$ and $g^{-1}$.
> [...] Put $k=[g,h]\in N\setminus\{1\}$.

* `exists_exponent_bound`, `exists_matrix_exponent_bound`: the bound `w`;
* `commutatorElement_mem_ne_one`: `k = [g, h] ∈ N ∖ {1}` for `g ∈ N` not commuting with `h`.
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic

open GroupApproximation.Pestov91
open scoped commutatorElement

/-- **`k = [g, h] ∈ N ∖ {1}`** (tex l.213): a commutator whose first entry lies in a normal
subgroup lies there, and it is `1` exactly when the two commute. -/
theorem commutatorElement_mem_ne_one {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {g h : G} (hg : g ∈ N) (hgh : ¬ Commute g h) : ⁅g, h⁆ ∈ N ∧ ⁅g, h⁆ ≠ 1 := by
  refine ⟨?_, fun h1 => hgh (commutatorElement_eq_one_iff_commute.mp h1)⟩
  rw [commutatorElement_def]
  exact SimpleModCentre.normal_comm_mem_left N hg h

section Exponents

/-- **A common exponent bound** for finitely many Laurent polynomials. -/
theorem exists_exponent_bound {A : Type*} [Ring A]
    (s : Finset (SkewMonoidAlgebra A (Multiplicative ℤ))) :
    ∃ w : ℕ, ∀ x ∈ s, ∀ j ∈ x.support, |Multiplicative.toAdd j| ≤ (w : ℤ) := by
  refine ⟨s.sup fun x => x.support.sup fun j => (Multiplicative.toAdd j).natAbs,
    fun x hx j hj => ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast (Finset.le_sup (f := fun j => (Multiplicative.toAdd j).natAbs) hj).trans
    (Finset.le_sup (f := fun x => x.support.sup fun j => (Multiplicative.toAdd j).natAbs) hx)

/-- **tex l.180–181**: `w ≥ 0` bounds the absolute values of the exponents in the entries of `g`
and `g⁻¹`. -/
theorem exists_matrix_exponent_bound {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A]
    (g : (Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ)))ˣ) :
    ∃ w : ℕ, ∀ (p q : ι) (j : Multiplicative ℤ),
      (j ∈ SkewMonoidAlgebra.support
          ((g : Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ))) p q) ∨
        j ∈ SkewMonoidAlgebra.support
          (((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ)))ˣ) :
            Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ))) p q)) →
        |Multiplicative.toAdd j| ≤ (w : ℤ) := by
  classical
  obtain ⟨w, hw⟩ := exists_exponent_bound
    ((Finset.univ : Finset (ι × ι)).image
        (fun pq => (g : Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ))) pq.1 pq.2) ∪
      (Finset.univ : Finset (ι × ι)).image
        (fun pq => ((g⁻¹ : (Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ)))ˣ) :
          Matrix ι ι (SkewMonoidAlgebra A (Multiplicative ℤ))) pq.1 pq.2))
  refine ⟨w, fun p q j hj => ?_⟩
  rcases hj with hj | hj
  · exact hw _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, rfl⟩)) j hj
  · exact hw _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, rfl⟩)) j hj

end Exponents

end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.commutatorElement_mem_ne_one
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_exponent_bound
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.exists_matrix_exponent_bound
