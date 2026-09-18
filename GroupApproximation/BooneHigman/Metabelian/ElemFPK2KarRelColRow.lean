import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Column and row words in a Steinberg group

Lane `bh-met-92u`, column/row module.  Over a commutative ring `R`, for distinct `i, j` and a
third index `p`:

* `col(p; ci, cj) = x_jp(cj) · x_ip(ci)` (`k2KarRel_col`);
* `row(p; ri, rj) = x_pi(ri) · x_pj(rj)` (`k2KarRel_row`).

Proved from the Steinberg relations alone:

* `k2KarRel_commute`: `col(p; c)` and `row(q; r)` commute if `p ≠ q` and `ri ci + rj cj = 0`;
* `k2KarRel_col_comm`: `⁅col(l; c), x_lk(σ)⁆ = col(k; c σ)`;
* `k2KarRel_comm_row`: `⁅x_lk(σ), row(k; r)⁆ = row(l; σ r)`;
* both words are natural under `indexMap`.

A numeric matrix check over `ℤ/101`, `n = 5`, is `truth_check.py` in the lane scratch folder.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarRelColRow

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]

/-- The column word `x_jp(cj) · x_ip(ci)`. -/
def k2KarRel_col (p i j : I) (hip : i ≠ p) (hjp : j ≠ p) (ci cj : R) : SteinbergGroup I R :=
  x j p hjp cj * x i p hip ci

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_col

/-- The row word `x_pi(ri) · x_pj(rj)`. -/
def k2KarRel_row (p i j : I) (hpi : p ≠ i) (hpj : p ≠ j) (ri rj : R) : SteinbergGroup I R :=
  x p i hpi ri * x p j hpj rj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_row

/-- Conjugating a column by a row at another index: if `ri ci + rj cj = 0`, nothing moves. -/
theorem k2KarRel_row_conj_col (p q i j : I) (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p)
    (hqi : q ≠ i) (hqj : q ≠ j) (hqp : q ≠ p) {ci cj ri rj : R}
    (h : ri * ci + rj * cj = 0) :
    k2KarRel_row q i j hqi hqj ri rj * k2KarRel_col p i j hip hjp ci cj *
        (k2KarRel_row q i j hqi hqj ri rj)⁻¹ = k2KarRel_col p i j hip hjp ci cj := by
  have e1 : x q j hqj rj * k2KarRel_col p i j hip hjp ci cj * (x q j hqj rj)⁻¹ =
      x q p hqp (rj * cj) * x j p hjp cj * x i p hip ci := by
    rw [k2KarRel_col, k2KarNorm_conj_mul, k2KarNorm_C2 j p q hjp hqj hqp cj rj,
      k2KarNorm_conj_of_commute
        (x_commute_of_ne q j i p hqj hip (Ne.symm hij) (Ne.symm hqp) rj ci)]
  have e2 : x q i hqi ri * (x q p hqp (rj * cj) * x j p hjp cj * x i p hip ci) *
      (x q i hqi ri)⁻¹ =
        x q p hqp (rj * cj) * x j p hjp cj * (x q p hqp (ri * ci) * x i p hip ci) := by
    rw [k2KarNorm_conj_mul, k2KarNorm_conj_mul, k2KarNorm_C2 i p q hip hqi hqp ci ri,
      k2KarNorm_conj_of_commute
        (x_commute_of_ne q i q p hqi hqp (Ne.symm hqi) (Ne.symm hqp) ri (rj * cj)),
      k2KarNorm_conj_of_commute (x_commute_of_ne q i j p hqi hjp hij (Ne.symm hqp) ri cj)]
  have e3 := x_commute_of_ne j p q p hjp hqp (Ne.symm hqp) (Ne.symm hjp) cj (ri * ci)
  have e4 : rj * cj + ri * ci = 0 := by rw [add_comm]; exact h
  rw [k2KarRel_row, k2KarNorm_conj_conj, e1, e2]
  calc x q p hqp (rj * cj) * x j p hjp cj * (x q p hqp (ri * ci) * x i p hip ci)
      = x q p hqp (rj * cj) * (x j p hjp cj * x q p hqp (ri * ci)) * x i p hip ci := by
        group
    _ = x q p hqp (rj * cj + ri * ci) * x j p hjp cj * x i p hip ci := by
        rw [e3.eq, ← x_mul]
        group
    _ = k2KarRel_col p i j hip hjp ci cj := by
        rw [e4, x_zero, one_mul, k2KarRel_col]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_row_conj_col

/-- A column and a row at different indices commute when `ri ci + rj cj = 0`. -/
theorem k2KarRel_commute (p q i j : I) (hij : i ≠ j) (hip : i ≠ p) (hjp : j ≠ p)
    (hqi : q ≠ i) (hqj : q ≠ j) (hqp : q ≠ p) {ci cj ri rj : R}
    (h : ri * ci + rj * cj = 0) :
    Commute (k2KarRel_col p i j hip hjp ci cj) (k2KarRel_row q i j hqi hqj ri rj) :=
  k2KarRel_commute_of_conj (k2KarRel_row_conj_col p q i j hij hip hjp hqi hqj hqp h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_commute

/-- Moving a column: `⁅col(l; ci, cj), x_lk(σ)⁆ = col(k; ci σ, cj σ)`. -/
theorem k2KarRel_col_comm (i j k l : I) (hik : i ≠ k) (hjk : j ≠ k) (hil : i ≠ l)
    (hjl : j ≠ l) (hlk : l ≠ k) (ci cj σ : R) :
    ⁅k2KarRel_col l i j hil hjl ci cj, x l k hlk σ⁆ =
      k2KarRel_col k i j hik hjk (ci * σ) (cj * σ) := by
  have e : ⁅k2KarRel_col l i j hil hjl ci cj, x l k hlk σ⁆ =
      x j l hjl cj * ⁅x i l hil ci, x l k hlk σ⁆ * (x j l hjl cj)⁻¹ *
        ⁅x j l hjl cj, x l k hlk σ⁆ := by
    rw [k2KarRel_col]
    simp only [commutatorElement_def]
    group
  rw [e, x_commutator i l k hil hlk hik, x_commutator j l k hjl hlk hjk,
    k2KarNorm_conj_of_commute
      (x_commute_of_ne j l i k hjl hik (Ne.symm hil) (Ne.symm hjk) cj (ci * σ)),
    (x_commute_of_ne i k j k hik hjk (Ne.symm hjk) (Ne.symm hik) (ci * σ) (cj * σ)).eq,
    k2KarRel_col]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_col_comm

/-- Moving a row: `⁅x_lk(σ), row(k; ri, rj)⁆ = row(l; σ ri, σ rj)`. -/
theorem k2KarRel_comm_row (i j k l : I) (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i)
    (hlj : l ≠ j) (hlk : l ≠ k) (σ ri rj : R) :
    ⁅x l k hlk σ, k2KarRel_row k i j hki hkj ri rj⁆ =
      k2KarRel_row l i j hli hlj (σ * ri) (σ * rj) := by
  have e : ⁅x l k hlk σ, k2KarRel_row k i j hki hkj ri rj⁆ =
      ⁅x l k hlk σ, x k i hki ri⁆ *
        (x k i hki ri * ⁅x l k hlk σ, x k j hkj rj⁆ * (x k i hki ri)⁻¹) := by
    rw [k2KarRel_row]
    simp only [commutatorElement_def]
    group
  rw [e, x_commutator l k i hlk hki hli, x_commutator l k j hlk hkj hlj,
    k2KarNorm_conj_of_commute
      (x_commute_of_ne k i l j hki hlj (Ne.symm hli) (Ne.symm hkj) ri (σ * rj)),
    k2KarRel_row]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_comm_row

end KarRelColRow

end GroupApproximation.BooneHigman.Metabelian.ElemFP
