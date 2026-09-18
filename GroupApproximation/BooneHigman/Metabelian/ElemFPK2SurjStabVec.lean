import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjCol
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, column side: padded matrices on `(u, t)` (lane bh-met-54)

Here `R` is an arbitrary unital ring.  `surjStabVec u t : R^{n+1}` is the vector `(u, t)`.
For `g : St_n(R)` and `v : R^n`, write `padMat` for the elementary matrix.  Then:

* `padMat (stab g) *ᵥ (u, t) = (padMat g *ᵥ u, t)`;
* `padMat (padCol v) *ᵥ (u, 0) = (u, 0)`;
* `padMat (padCol v) *ᵥ (u, 1) = (u + v, 1)`.

The first formula is proved by closure induction over the Steinberg generators.  The other
two are proved by `Pi.single` induction on `v`.  Module `ElemFPK2SurjStabReduce` uses them to
show `K₂ ∩ (stab St_n · padCol R^n) ⊆ stab K₂(n)`.

Truth check.  With `t = 1` and `x_{p,last}(a)`, the formula reads `(1 + e_{p,last}(a)) (u, 1) =
(u + a e_p, 1)`.  This is correct, and so is `t = 0`, which is fixed.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- The vector `(u, t) : R^{n+1}`. -/
def surjStabVec (u : Fin n → R) (t : R) : Fin (n + 1) → R :=
  Fin.snoc (α := fun _ => R) u t

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabVec

theorem surjStabVec_castSucc (u : Fin n → R) (t : R) (i : Fin n) :
    surjStabVec u t i.castSucc = u i :=
  Fin.snoc_castSucc (α := fun _ => R) t u i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabVec_castSucc

theorem surjStabVec_last (u : Fin n → R) (t : R) : surjStabVec u t (Fin.last n) = t :=
  Fin.snoc_last (α := fun _ => R) t u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabVec_last

theorem surjStabVec_inj {u u' : Fin n → R} {t t' : R} (h : surjStabVec u t = surjStabVec u' t') :
    u = u' := by
  funext i
  have e := congrFun h i.castSucc
  rw [surjStabVec_castSucc, surjStabVec_castSucc] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabVec_inj

theorem surjStabVec_add_single (u : Fin n → R) (t : R) (p : Fin n) (c : R) :
    surjStabVec (u + Pi.single p c) t = surjStabVec u t + Pi.single p.castSucc c := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · rw [Pi.add_apply, surjStabVec_castSucc, surjStabVec_castSucc, Pi.add_apply]
    by_cases hip : i = p
    · rw [hip, Pi.single_eq_same, Pi.single_eq_same]
    · have hcs : i.castSucc ≠ p.castSucc := fun e => hip (Fin.castSucc_inj.mp e)
      rw [Pi.single_eq_of_ne hip, Pi.single_eq_of_ne hcs]
  · have hl : Fin.last n ≠ p.castSucc := (Fin.castSucc_lt_last p).ne'
    rw [Pi.add_apply, surjStabVec_last, surjStabVec_last, Pi.single_eq_of_ne hl, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabVec_add_single

/-- Generator case of `surjStab_stab_mulVec`. -/
theorem surjStab_stab_x_mulVec (i j : Fin n) (hij : i ≠ j) (b : R) (u : Fin n → R) (t : R) :
    padMat (stab n R (x i j hij b)) *ᵥ surjStabVec u t =
      surjStabVec (padMat (x i j hij b) *ᵥ u) t := by
  rw [stab_x, padMat_x, padMat_x]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi]
  rw [surjStabVec_castSucc, surjStabVec_add_single]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_stab_x_mulVec

/-- `padMat (stab g) *ᵥ (u, t) = (padMat g *ᵥ u, t)`. -/
theorem surjStab_stab_mulVec (g : St n R) (u : Fin n → R) (t : R) :
    padMat (stab n R g) *ᵥ surjStabVec u t = surjStabVec (padMat g *ᵥ u) t := by
  have hg := mem_closure_range_of (R := R) g
  revert u
  induction hg using Subgroup.closure_induction'' with
  | mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    exact fun u => surjStab_stab_x_mulVec i j hij b u t
  | inv_mem g hx =>
    obtain ⟨⟨i, j, hij, b⟩, rfl⟩ := hx
    intro u
    have e := surjStab_stab_x_mulVec i j hij (-b) u t
    rw [x_neg] at e
    exact e
  | one =>
    intro u
    simp only [map_one, Matrix.one_mulVec]
  | mul g h _ _ hg hh =>
    intro u
    rw [map_mul (stab n R) g h, map_mul padMat (stab n R g) (stab n R h), map_mul padMat g h,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh u, hg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_stab_mulVec

/-- `padMat (padCol v) *ᵥ (u, 0) = (u, 0)`. -/
theorem surjStab_padCol_mulVec_zero (v u : Fin n → R) :
    padMat (padCol v) *ᵥ surjStabVec u 0 = surjStabVec u 0 := by
  induction v using Pi.single_induction with
  | zero => rw [padCol_zero, map_one, Matrix.one_mulVec]
  | add f g hf hg =>
    rw [padCol_add, map_mul padMat (padCol f) (padCol g), ← Matrix.mulVec_mulVec, hg, hf]
  | single p a =>
    rw [padCol_single, padMat_x]
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi, surjStabVec_last,
      mul_zero, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_padCol_mulVec_zero

/-- `padMat (padCol v) *ᵥ (u, 1) = (u + v, 1)`. -/
theorem surjStab_padCol_mulVec_one (v u : Fin n → R) :
    padMat (padCol v) *ᵥ surjStabVec u 1 = surjStabVec (u + v) 1 := by
  induction v using Pi.single_induction generalizing u with
  | zero => rw [padCol_zero, map_one, Matrix.one_mulVec, add_zero]
  | add f g hf hg =>
    rw [padCol_add, map_mul padMat (padCol f) (padCol g), ← Matrix.mulVec_mulVec, hg u,
      hf (u + g), show u + g + f = u + (f + g) by abel]
  | single p a =>
    rw [padCol_single, padMat_x]
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec_eq_pi, surjStabVec_last,
      mul_one]
    exact (surjStabVec_add_single u 1 p a).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStab_padCol_mulVec_one

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
