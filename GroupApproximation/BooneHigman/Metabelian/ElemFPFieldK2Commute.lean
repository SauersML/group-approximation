import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2Central
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg symbols commute with everything

Lane `bh-met-15`.  `symbol_conj_x` puts the seven root cases of `ElemFPFieldK2Central` together:
the symbol fixes every root element `x_pq(t)` under conjugation.  `symbol_commute` then shows it
commutes with every element of `St_I(R)`, because the root elements generate the presented group.
Both need a third index `k ∉ {i, j}`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (x_congr)

variable {I R : Type*} [Fintype I] [DecidableEq I] [Field R]

/-- The symbol fixes every root element under conjugation. -/
theorem symbol_conj_x (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ)
    (p q : I) (hpq : p ≠ q) (t : R) :
    symbol i j hij u v * x p q hpq t * (symbol i j hij u v)⁻¹ = x p q hpq t := by
  by_cases hpi : p = i
  · have hiq : i ≠ q := fun e => hpq (hpi.trans e)
    by_cases hqj : q = j
    · rw [x_congr hpq hij hpi hqj (rfl : t = t)]
      exact symbol_conj_ij i j hij u v k hik hjk t
    · have hjq : j ≠ q := fun e => hqj e.symm
      rw [x_congr hpq hiq hpi (rfl : q = q) (rfl : t = t)]
      exact symbol_conj_iq i j hij u v q hiq hjq t
  by_cases hpj : p = j
  · have hjq : j ≠ q := fun e => hpq (hpj.trans e)
    by_cases hqi : q = i
    · rw [x_congr hpq hij.symm hpj hqi (rfl : t = t)]
      exact symbol_conj_ji i j hij u v k hik hjk t
    · have hiq : i ≠ q := fun e => hqi e.symm
      rw [x_congr hpq hjq hpj (rfl : q = q) (rfl : t = t)]
      exact symbol_conj_jq i j hij u v q hiq hjq t
  by_cases hqi : q = i
  · rw [x_congr hpq hpi (rfl : p = p) hqi (rfl : t = t)]
    exact symbol_conj_pi i j hij u v p hpi hpj t
  by_cases hqj : q = j
  · rw [x_congr hpq hpj (rfl : p = p) hqj (rfl : t = t)]
    exact symbol_conj_pj i j hij u v p hpi hpj t
  exact symbol_conj_pq i j hij u v p q hpq (fun e => hpi e.symm) (fun e => hpj e.symm)
    (fun e => hqi e.symm) (fun e => hqj e.symm) t

/-- **Centrality.**  The symbol commutes with every element of the Steinberg group. -/
theorem symbol_commute (i j k : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (u v : Rˣ)
    (g : SteinbergGroup I R) : Commute (symbol i j hij u v) g := by
  have hg : g ∈ Subgroup.centralizer ({symbol i j hij u v} : Set (SteinbergGroup I R)) := by
    refine PresentedGroup.generated_by _ _ (fun gen => ?_) g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp (symbol_conj_x i j k hij hik hjk u v gen.row gen.column
      gen.row_ne_column gen.coefficient)).symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_conj_x
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.symbol_commute
