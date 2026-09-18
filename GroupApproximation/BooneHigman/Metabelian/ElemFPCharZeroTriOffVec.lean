import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffFix
import GroupApproximation.Meta.AxiomGuard

/-!
# Padded row and column matrices on `(u, t)` for general `t` (lane bh-met-90l)

Here `surjStabVec u t = (u, t) : R^{n+1}`.  This file proves:

* `padMat (padRow w) (u, t) = (u, t + w ⬝ u)`;
* `(u, t) padMat (padRow w) = (u + t w, t)`;
* `padMat (padCol v) (u, t) = (u + t v, t)` over a commutative ring;
* `(u, t) ⬝ (u', t') = u ⬝ u' + t t'`, together with the eta rule `y = (y|_n, y_last)`.

It also records the vanishing of `M e_L` and `e_L M` at an index `c ≠ L`, when `M` is the
matrix of an element of the root subgroup avoiding `c`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `t • e_p(a) = e_p(t a)`. -/
theorem czTriOff_smul_single (t a : R) (p : Fin n) :
    t • (Pi.single p a : Fin n → R) = Pi.single p (t * a) := by
  funext q
  by_cases hq : q = p
  · subst hq
    rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq, smul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_smul_single

/-- `(0, 1) = e_last`. -/
theorem czTriOff_e_eq : surjStabVec (0 : Fin n → R) 1 = Pi.single (Fin.last n) 1 := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · rw [surjStabVec_castSucc, Pi.zero_apply, Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne]
  · rw [surjStabVec_last, Pi.single_eq_same]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_e_eq

/-- Eta rule: every vector is `(y|_n, y_last)`. -/
theorem czTriOff_eta (y : Fin (n + 1) → R) :
    surjStabVec (fun p => y p.castSucc) (y (Fin.last n)) = y := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · exact surjStabVec_castSucc _ _ i
  · exact surjStabVec_last _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_eta

/-- `(a, t) ⬝ (b, u) = a ⬝ b + t u`. -/
theorem czTriOff_dot_split (a b : Fin n → R) (t u : R) :
    surjStabVec a t ⬝ᵥ surjStabVec b u = a ⬝ᵥ b + t * u := by
  simp only [dotProduct, Fin.sum_univ_castSucc, surjStabVec_castSucc, surjStabVec_last]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_dot_split

/-- `padMat (padRow w) (u, t) = (u, t + w ⬝ u)`. -/
theorem czTriOff_padRow_mulVec (w u : Fin n → R) (t : R) :
    padMat (padRow w) *ᵥ surjStabVec u t = surjStabVec u (t + w ⬝ᵥ u) := by
  induction w using Pi.single_induction generalizing t with
  | zero => rw [padRow_zero, map_one, Matrix.one_mulVec, zero_dotProduct, add_zero]
  | add f g hf hg =>
    rw [padRow_add, map_mul padMat (padRow f) (padRow g), ← Matrix.mulVec_mulVec, hg t,
      hf (t + g ⬝ᵥ u), add_dotProduct, add_assoc, add_comm (g ⬝ᵥ u) (f ⬝ᵥ u)]
  | single p a =>
    rw [padRow_single, padMat_x, Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi,
      surjStabVec_castSucc, surjStabFactor_vec_add_last, single_dotProduct]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padRow_mulVec

/-- `(u, t) padMat (padRow w) = (u + t w, t)`. -/
theorem czTriOff_vecMul_padRow (w u : Fin n → R) (t : R) :
    surjStabVec u t ᵥ* padMat (padRow w) = surjStabVec (u + t • w) t := by
  induction w using Pi.single_induction generalizing u with
  | zero => rw [padRow_zero, map_one, Matrix.vecMul_one, smul_zero, add_zero]
  | add f g hf hg =>
    rw [padRow_add, map_mul padMat (padRow f) (padRow g), ← Matrix.vecMul_vecMul, hf u,
      hg (u + t • f), smul_add, add_assoc]
  | single p a =>
    rw [padRow_single, padMat_x, Matrix.vecMul_add, Matrix.vecMul_one, surjStab_vecMul_single,
      surjStabVec_last, czTriOff_smul_single, surjStabVec_add_single]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_vecMul_padRow

/-- `padMat (padCol v) (u, t) = (u + t v, t)` over a commutative ring. -/
theorem czTriOff_padCol_mulVec {S : Type*} [CommRing S] (v u : Fin n → S) (t : S) :
    padMat (padCol v) *ᵥ surjStabVec u t = surjStabVec (u + t • v) t := by
  induction v using Pi.single_induction generalizing u with
  | zero => rw [padCol_zero, map_one, Matrix.one_mulVec, smul_zero, add_zero]
  | add f g hf hg =>
    rw [padCol_add, map_mul padMat (padCol f) (padCol g), ← Matrix.mulVec_mulVec, hg u,
      hf (u + t • g), smul_add, add_assoc, add_comm (t • g) (t • f)]
  | single p a =>
    rw [padCol_single, padMat_x, Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi,
      surjStabVec_last, czTriOff_smul_single, mul_comm t a, surjStabVec_add_single]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padCol_mulVec

/-- The last column of a matrix avoiding `c ≠ last` vanishes at `c`. -/
theorem czTriOff_mulVec_eq_zero {c : Fin (n + 1)} {g : St (n + 1) R}
    (hg : g ∈ czStabGen_off R c) (hc : c ≠ Fin.last n) :
    (padMat g *ᵥ surjStabVec (0 : Fin n → R) 1) c = 0 := by
  rw [czTriOff_e_eq]
  have h := czTriOff_fix_vecMul_apply (czTriOff_fix_of_mem hg) (Pi.single (Fin.last n) (1 : R))
  rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hc] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_mulVec_eq_zero

/-- The last row of a matrix avoiding `c ≠ last` vanishes at `c`. -/
theorem czTriOff_vecMul_eq_zero {c : Fin (n + 1)} {g : St (n + 1) R}
    (hg : g ∈ czStabGen_off R c) (hc : c ≠ Fin.last n) :
    (surjStabVec (0 : Fin n → R) 1 ᵥ* padMat g) c = 0 := by
  rw [czTriOff_e_eq]
  have h := czTriOff_fix_mulVec_apply (czTriOff_fix_of_mem hg) (Pi.single (Fin.last n) (1 : R))
  rw [dotProduct_single, mul_one, Pi.single_eq_of_ne hc] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_vecMul_eq_zero

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
