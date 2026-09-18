import Mathlib.Tactic.LinearCombination
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelColRow
import GroupApproximation.Meta.AxiomGuard

/-!
# Balancing a scalar between a column and a row

Lane `bh-met-92u`, balance module.  Take four distinct indices `i, j, k, l` and entries with
`ri ci + rj cj = 0`.  Put `e = col(l; ci, cj)`, `f = x_lk(σ)` and `g = row(k; ri, rj)`.  Then
`⁅e, f⁆ = col(k; ci σ, cj σ)` and `⁅f, g⁆ = row(l; σ ri, σ rj)`.  Both pairs `(e, g)` and
`(⁅e, f⁆, ⁅f, g⁆)` are a column and a row at different indices whose entries pair to `0`, so
they commute (`k2KarRel_commute`).  The swap lemma `k2KarRel_comm_swap` then gives

* `k2KarRel_swap`: `⁅col(k; c σ), row(k; r)⁆ = ⁅row(l; σ r)⁻¹, col(l; c)⁆`.

With `σ = 1` the same identity applies to `(c, σ r)`, so

* `k2KarRel_balance`: `⁅col(k; c σ), row(k; r)⁆ = ⁅col(k; c), row(k; σ r)⁆`.

The fourth index `l` is essential: it is the auxiliary index that carries `σ`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarRelBalance

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- **Swap** through a fourth index `l`. -/
theorem k2KarRel_swap (i j k l : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hil : i ≠ l)
    (hjl : j ≠ l) (hkl : k ≠ l) {ci cj ri rj : R} (σ : R) (h : ri * ci + rj * cj = 0) :
    ⁅k2KarRel_col k i j hik hjk (ci * σ) (cj * σ), k2KarRel_row k i j hik.symm hjk.symm ri rj⁆ =
      ⁅(k2KarRel_row l i j hil.symm hjl.symm (σ * ri) (σ * rj))⁻¹,
        k2KarRel_col l i j hil hjl ci cj⁆ := by
  have heg := (k2KarRel_commute l k i j hij hil hjl hik.symm hjk.symm hkl h).eq
  have h' : σ * ri * (ci * σ) + σ * rj * (cj * σ) = 0 := by
    linear_combination (σ * σ) * h
  have hxy := (k2KarRel_commute k l i j hij hik hjk hil.symm hjl.symm hkl.symm h').eq
  rw [← k2KarRel_col_comm i j k l hik hjk hil hjl hkl.symm ci cj σ,
    ← k2KarRel_comm_row i j k l hik.symm hjk.symm hil.symm hjl.symm hkl.symm σ ri rj] at hxy ⊢
  exact k2KarRel_comm_swap heg hxy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_swap

/-- **Balance**: a scalar moves from the column to the row, given a fourth index. -/
theorem k2KarRel_balance (i j k l : I) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) {ci cj ri rj : R} (σ : R)
    (h : ri * ci + rj * cj = 0) :
    ⁅k2KarRel_col k i j hik hjk (ci * σ) (cj * σ), k2KarRel_row k i j hik.symm hjk.symm ri rj⁆ =
      ⁅k2KarRel_col k i j hik hjk ci cj,
        k2KarRel_row k i j hik.symm hjk.symm (σ * ri) (σ * rj)⁆ := by
  have h1 : σ * ri * ci + σ * rj * cj = 0 := by
    linear_combination σ * h
  have e := k2KarRel_swap i j k l hij hik hjk hil hjl hkl 1 h1
  simp only [mul_one, one_mul] at e
  rw [k2KarRel_swap i j k l hij hik hjk hil hjl hkl σ h]
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_balance

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem k2KarRel_indexMap_col (e : I ↪ J) (p i j : I) (hip : i ≠ p) (hjp : j ≠ p)
    (ci cj : R) :
    indexMap e (k2KarRel_col p i j hip hjp ci cj) =
      k2KarRel_col (e p) (e i) (e j) (e.injective.ne hip) (e.injective.ne hjp) ci cj := by
  simp only [k2KarRel_col, map_mul, indexMap_x]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_indexMap_col

theorem k2KarRel_indexMap_row (e : I ↪ J) (p i j : I) (hpi : p ≠ i) (hpj : p ≠ j)
    (ri rj : R) :
    indexMap e (k2KarRel_row p i j hpi hpj ri rj) =
      k2KarRel_row (e p) (e i) (e j) (e.injective.ne hpi) (e.injective.ne hpj) ri rj := by
  simp only [k2KarRel_row, map_mul, indexMap_x]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_indexMap_row

end KarRelBalance

end GroupApproximation.BooneHigman.Metabelian.ElemFP
