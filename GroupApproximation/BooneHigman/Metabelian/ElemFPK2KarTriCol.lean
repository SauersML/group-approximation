import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriRow
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjCol
import GroupApproximation.Meta.AxiomGuard

/-!
# Last-column commutators `⁅padCol v, x_{N,j}(ω)⁆` with `v_j = 0`

Lane `bh-met-93k`, column module (mirror of `ElemFPK2KarTriRow`).  With `N = Fin.last n`:

* `k2KarTri_col_commute`: `⁅padCol (off j v), x_{N,j}(ω)⁆` commutes with every
  `padCol (off j v')` (it is a product of roots `x_{p,j}`, `p ≠ j`);
* `k2KarTri_col_add`: `⁅padCol (u + v), x_{N,j}(ω)⁆ = ⁅padCol v, x_{N,j}(ω)⁆ ⁅padCol u, x_{N,j}(ω)⁆`
  when `u_j = v_j = 0`;
* `k2KarTri_col_smul` (commutative `R`): `⁅padCol v, x_{N,j}(ω)⁆ = ⁅padCol (ω • v), x_{N,j}(1)⁆`
  when `v_j = 0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped commutatorElement

section KarTriColRing

variable {R : Type*} [Ring R] {n : ℕ}

/-- A root `x_{p,j}` commutes with `padCol (off j v)`. -/
theorem k2KarTri_x_commute_padCol_off (j p : Fin n) (hcs : p.castSucc ≠ j.castSucc) (a : R)
    (v : Fin n → R) :
    Commute (x p.castSucc j.castSucc hcs a) (padCol (k2KarTri_off j v)) := by
  induction v using Pi.single_induction with
  | zero =>
    rw [k2KarTri_off_zero, padCol_zero]
    exact Commute.one_right _
  | add f g hf hg =>
    rw [k2KarTri_off_add, padCol_add]
    exact hf.mul_right hg
  | single q b =>
    by_cases hq : q = j
    · rw [hq, k2KarTri_off_single_self, padCol_zero]
      exact Commute.one_right _
    · rw [k2KarTri_off_single_of_ne hq, padCol_single]
      exact x_commute_of_ne p.castSucc j.castSucc q.castSucc (Fin.last n) hcs
        (Fin.castSucc_lt_last q).ne (fun e ↦ hq (Fin.castSucc_inj.mp e).symm)
        (Fin.castSucc_lt_last p).ne' a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_x_commute_padCol_off

/-- `⁅padCol (off j v), x_{N,j}(ω)⁆` commutes with every `padCol (off j v')`. -/
theorem k2KarTri_col_commute (j : Fin n) (ω : R) (v : Fin n → R) :
    ∀ v' : Fin n → R, Commute ⁅padCol (k2KarTri_off j v),
      x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' ω⁆ (padCol (k2KarTri_off j v')) := by
  induction v using Pi.single_induction with
  | zero =>
    intro v'
    rw [k2KarTri_off_zero, padCol_zero, commutatorElement_one_left]
    exact Commute.one_left _
  | add f g hf hg =>
    intro v'
    rw [k2KarTri_off_add, padCol_add, k2KarTri_mul_comm_of_commute _ _ _ (hg f)]
    exact (hg v').mul_left (hf v')
  | single q a =>
    intro v'
    by_cases hq : q = j
    · rw [hq, k2KarTri_off_single_self, padCol_zero, commutatorElement_one_left]
      exact Commute.one_left _
    · rw [k2KarTri_off_single_of_ne hq, padCol_single,
        x_commutator q.castSucc (Fin.last n) j.castSucc (Fin.castSucc_lt_last q).ne
          (Fin.castSucc_lt_last j).ne' (fun e ↦ hq (Fin.castSucc_inj.mp e)) a ω]
      exact k2KarTri_x_commute_padCol_off j q _ (a * ω) v'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_col_commute

/-- Additivity of `v ↦ ⁅padCol v, x_{N,j}(ω)⁆` on vectors with vanishing `j`-th entry. -/
theorem k2KarTri_col_add (j : Fin n) (ω : R) {u v : Fin n → R} (hu : u j = 0) (hv : v j = 0) :
    ⁅padCol (u + v), x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' ω⁆ =
      ⁅padCol v, x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' ω⁆ *
        ⁅padCol u, x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' ω⁆ := by
  have hc := k2KarTri_col_commute j ω v u
  rw [k2KarTri_off_of_apply hv, k2KarTri_off_of_apply hu] at hc
  rw [padCol_add, k2KarTri_mul_comm_of_commute _ _ _ hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_col_add

end KarTriColRing

section KarTriColComm

variable {R : Type*} [CommRing R] {n : ℕ}

theorem k2KarTri_col_smul_off (j : Fin n) (ω : R) (v : Fin n → R) :
    ⁅padCol (k2KarTri_off j v), x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' ω⁆ =
      ⁅padCol (ω • k2KarTri_off j v),
        x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' 1⁆ := by
  induction v using Pi.single_induction with
  | zero =>
    rw [k2KarTri_off_zero, smul_zero, padCol_zero, commutatorElement_one_left,
      commutatorElement_one_left]
  | add f g hf hg =>
    have hc := k2KarTri_col_commute j (1 : R) (ω • g) (ω • f)
    rw [← k2KarTri_smul_off, ← k2KarTri_smul_off] at hc
    rw [k2KarTri_off_add, smul_add, padCol_add, padCol_add,
      k2KarTri_mul_comm_of_commute _ _ _ (k2KarTri_col_commute j ω g f),
      k2KarTri_mul_comm_of_commute _ _ _ hc, hf, hg]
  | single q a =>
    by_cases hq : q = j
    · rw [hq, k2KarTri_off_single_self, smul_zero, padCol_zero, commutatorElement_one_left,
        commutatorElement_one_left]
    · rw [k2KarTri_off_single_of_ne hq, k2KarTri_smul_single, padCol_single, padCol_single,
        x_commutator q.castSucc (Fin.last n) j.castSucc (Fin.castSucc_lt_last q).ne
          (Fin.castSucc_lt_last j).ne' (fun e ↦ hq (Fin.castSucc_inj.mp e)) a ω,
        x_commutator q.castSucc (Fin.last n) j.castSucc (Fin.castSucc_lt_last q).ne
          (Fin.castSucc_lt_last j).ne' (fun e ↦ hq (Fin.castSucc_inj.mp e)) (ω * a) 1,
        mul_one, mul_comm a ω]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_col_smul_off

/-- `⁅padCol v, x_{N,j}(ω)⁆ = ⁅padCol (ω • v), x_{N,j}(1)⁆` when `v_j = 0`. -/
theorem k2KarTri_col_smul (j : Fin n) (ω : R) {v : Fin n → R} (hv : v j = 0) :
    ⁅padCol v, x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' ω⁆ =
      ⁅padCol (ω • v), x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' 1⁆ := by
  have e := k2KarTri_col_smul_off j ω v
  rwa [k2KarTri_off_of_apply hv] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_col_smul

end KarTriColComm

end GroupApproximation.BooneHigman.Metabelian.ElemFP
