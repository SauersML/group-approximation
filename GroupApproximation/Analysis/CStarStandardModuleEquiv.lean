import GroupApproximation.Analysis.CStarStandardModule
import GroupApproximation.Analysis.CStarUnitary
import GroupApproximation.Analysis.CStarDirectSumOperators

/-!
# `H_B` is stable: `H_B ⊕ H_B ≅ H_B`

Two unitaries, and one corollary.

* `reindex` --- a bijection `ι ≃ κ` induces a unitary
  `H_B(ι) ≅ H_B(κ)`.  Unconditional convergence is what makes this true: the
  sums defining the inner products are over *finite subsets*, so a
  re-indexing does not disturb them.  (This is precisely the property the
  `unconditional` summation filter records, and it is why `H_B` is defined
  with `Summable` and not with a series over `ℕ`.)
* `sumMerge` --- `H_B(ι) ⊞ H_B(κ) ≅ H_B(ι ⊕ κ)`, the statement that the
  direct sum of two standard modules is the standard module on the disjoint
  union.  Both directions of summability are `Summable.sum` and
  `Summable.comp_injective`, and the inner-product identity is
  `Summable.tsum_sum`.
* `natSumMerge` --- their composite with `ℕ ⊕ ℕ ≃ ℕ`: **`H_B ⊞ H_B ≅ H_B`.**

## Why this is the first half of stabilization

Kasparov's theorem says `H_B ⊕ E ≅ H_B` for every countably generated `E`.
The case `E = H_B` is the statement proved here, and it is the only case that
is formal: for general `E` the isomorphism is built from a dense sequence in
`E` by the Mingo--Phillips argument, and nothing in that argument is
re-indexing.  So this file closes the part of stabilization that is
bookkeeping and leaves exactly the part that is a theorem.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe u u' v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

namespace Adjointable

/-! ## Re-indexing -/

/-- **A bijection of index sets induces a unitary of standard modules.** -/
def reindex {ι : Type u} {κ : Type u'} (e : ι ≃ κ) :
    Adjointable (standardModule ι B) (standardModule κ B) where
  toFun f := ⟨fun k => f.1 (e.symm k), by
    have h : Summable fun i => star (f.1 i) * f.1 i := f.2
    exact (Equiv.summable_iff e.symm).mpr h⟩
  adj g := ⟨fun i => g.1 (e i), by
    have h : Summable fun k => star (g.1 k) * g.1 k := g.2
    exact (Equiv.summable_iff e).mpr h⟩
  inner_adj f g := by
    show (∑' k, star (f.1 (e.symm k)) * g.1 k)
        = ∑' i, star (f.1 i) * g.1 (e i)
    rw [← Equiv.tsum_eq e fun k => star (f.1 (e.symm k)) * g.1 k]
    refine tsum_congr fun i => ?_
    rw [Equiv.symm_apply_apply]

@[simp] theorem reindex_toFun {ι : Type u} {κ : Type u'} (e : ι ≃ κ)
    (f : (standardModule ι B).carrier) (k : κ) :
    ((reindex e).toFun f).1 k = f.1 (e.symm k) := rfl

theorem isUnitaryAdj_reindex {ι : Type u} {κ : Type u'} (e : ι ≃ κ) :
    (reindex (B := B) e).IsUnitaryAdj where
  adj_toFun f := by
    refine Subtype.ext (funext fun i => ?_)
    show f.1 (e.symm (e i)) = f.1 i
    rw [Equiv.symm_apply_apply]
  toFun_adj g := by
    refine Subtype.ext (funext fun k => ?_)
    show g.1 (e (e.symm k)) = g.1 k
    rw [Equiv.apply_symm_apply]

/-! ## Merging two standard modules -/

/-- **The direct sum of two standard modules is the standard module on the
disjoint union.** -/
def sumMerge (ι : Type u) (κ : Type u) (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :
    Adjointable (prod (standardModule ι B) (standardModule κ B))
      (standardModule (ι ⊕ κ) B) where
  toFun p := ⟨Sum.elim p.1.1 p.2.1, by
    exact Summable.sum _ p.1.2 p.2.2⟩
  adj h :=
    (⟨fun i => h.1 (Sum.inl i), by
        exact h.2.comp_injective Sum.inl_injective⟩,
     ⟨fun j => h.1 (Sum.inr j), by
        exact h.2.comp_injective Sum.inr_injective⟩)
  inner_adj p h := by
    show (∑' s, star (Sum.elim p.1.1 p.2.1 s) * h.1 s)
        = (∑' i, star (p.1.1 i) * h.1 (Sum.inl i))
          + ∑' j, star (p.2.1 j) * h.1 (Sum.inr j)
    refine Summable.tsum_sum ?_ ?_
    · exact summable_star_mul p.1.2 (h.2.comp_injective Sum.inl_injective)
    · exact summable_star_mul p.2.2 (h.2.comp_injective Sum.inr_injective)

theorem isUnitaryAdj_sumMerge (ι : Type u) (κ : Type u) (B : Type v)
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    (sumMerge ι κ B).IsUnitaryAdj where
  adj_toFun p :=
    Prod.ext (Subtype.ext (funext fun _ => rfl))
      (Subtype.ext (funext fun _ => rfl))
  toFun_adj h := by
    refine Subtype.ext (funext fun s => ?_)
    cases s with
    | inl i => rfl
    | inr j => rfl

/-! ## `H_B ⊞ H_B ≅ H_B` -/

/-- **The standard module absorbs itself.**  This is the case `E = H_B` of
Kasparov's stabilization theorem, and the only case that is formal. -/
noncomputable def natSumMerge (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] :
    Adjointable (prod (standardModule ℕ B) (standardModule ℕ B))
      (standardModule ℕ B) :=
  (reindex Equiv.natSumNatEquivNat).comp (sumMerge ℕ ℕ B)

theorem isUnitaryAdj_natSumMerge (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] :
    (natSumMerge B).IsUnitaryAdj :=
  (isUnitaryAdj_reindex Equiv.natSumNatEquivNat).comp (isUnitaryAdj_sumMerge ℕ ℕ B)

end Adjointable

end HilbertModule
end GroupApproximation
