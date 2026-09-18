import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWiring
import GroupApproximation.Meta.AxiomGuard

/-!
# Nagao normal forms for `K₂(F_p[X])`, part 4: the explicit Euclidean section `σ`

Lane `bh-met-92q`.  Notation of `ElemFPK2PolyEuclidGen`; `R = F_p[X]`, two indices `m ≠ L`,
and `W' = w_mL(-1)`, which acts on the `(m, L)` coordinates by `(c, d) ↦ (-d, c)`.

* `k2PolyNagaoSigma_tau b`: `1` if `b = 1`, `h_mL(b)⁻¹` if `b` is another unit, `1` otherwise.
* `k2PolyNagaoSigma_pair a b` (well-founded recursion on `deg a`, `Polynomial.degree_lt_wf`):
  `pair 0 b = τ(b)` and, for `a ≠ 0`, `pair a b = x_Lm(b / a) · W' · pair (b % a) (-a)`.
  This is the Euclidean algorithm on the column `(a, b)`: `pair a b · e_L = (a, b)` for every
  unimodular column (checked in scratchpad `bh-met-92q/chk.py`).
* `k2PolyNagaoSigma_sigma v = pair (v m) (v L)`, with `σ(e_L) = 1`
  (`k2PolyNagaoSigma_sigma_unitVec`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (unitVec unitVec_apply)

variable {I : Type} [Fintype I] [DecidableEq I]

variable (p : ℕ) [Fact p.Prime]

open Classical in
/-- The base case of `σ`: `τ(1) = 1`, `τ(b) = h_mL(b)⁻¹` for a unit `b ≠ 1`, else `1`. -/
noncomputable def k2PolyNagaoSigma_tau (m L : I) (hmL : m ≠ L) (b : Polynomial (ZMod p)) :
    SteinbergGroup I (Polynomial (ZMod p)) :=
  if b = 1 then 1 else if hb : IsUnit b then (h m L hmL hb.unit)⁻¹ else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_tau

open Classical in
/-- One Euclidean step: `(a, b) ↦ x_Lm(b / a) · W' · rec (b % a) (-a)` for `a ≠ 0`. -/
noncomputable def k2PolyNagaoSigma_step (m L : I) (hmL : m ≠ L) (a : Polynomial (ZMod p))
    (rec : ∀ c : Polynomial (ZMod p), c.degree < a.degree → Polynomial (ZMod p) →
      SteinbergGroup I (Polynomial (ZMod p)))
    (b : Polynomial (ZMod p)) : SteinbergGroup I (Polynomial (ZMod p)) :=
  if ha : a = 0 then k2PolyNagaoSigma_tau p m L hmL b
  else x L m hmL.symm (b / a) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
    rec (b % a) (Polynomial.degree_mod_lt b ha) (-a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_step

/-- The Euclidean word of the column `(a, b)`, by well-founded recursion on `deg a`. -/
noncomputable def k2PolyNagaoSigma_pair (m L : I) (hmL : m ≠ L) :
    Polynomial (ZMod p) → Polynomial (ZMod p) → SteinbergGroup I (Polynomial (ZMod p)) :=
  WellFounded.fix
    (C := fun _ => Polynomial (ZMod p) → SteinbergGroup I (Polynomial (ZMod p)))
    (Polynomial.degree_lt_wf (R := ZMod p)) (k2PolyNagaoSigma_step p m L hmL)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_pair

/-- The unfolding equation of `k2PolyNagaoSigma_pair`. -/
theorem k2PolyNagaoSigma_pair_eq (m L : I) (hmL : m ≠ L) (a b : Polynomial (ZMod p)) :
    k2PolyNagaoSigma_pair p m L hmL a b =
      k2PolyNagaoSigma_step p m L hmL a (fun c _ => k2PolyNagaoSigma_pair p m L hmL c) b :=
  congrFun (WellFounded.fix_eq
    (C := fun _ => Polynomial (ZMod p) → SteinbergGroup I (Polynomial (ZMod p)))
    (Polynomial.degree_lt_wf (R := ZMod p)) (k2PolyNagaoSigma_step p m L hmL) a) b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_pair_eq

/-- `pair 0 b = τ(b)`. -/
theorem k2PolyNagaoSigma_pair_zero (m L : I) (hmL : m ≠ L) (b : Polynomial (ZMod p)) :
    k2PolyNagaoSigma_pair p m L hmL 0 b = k2PolyNagaoSigma_tau p m L hmL b := by
  rw [k2PolyNagaoSigma_pair_eq p m L hmL 0 b, k2PolyNagaoSigma_step, dif_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_pair_zero

/-- `pair a b = x_Lm(b / a) · W' · pair (b % a) (-a)` for `a ≠ 0`. -/
theorem k2PolyNagaoSigma_pair_of_ne (m L : I) (hmL : m ≠ L) {a : Polynomial (ZMod p)}
    (ha : a ≠ 0) (b : Polynomial (ZMod p)) :
    k2PolyNagaoSigma_pair p m L hmL a b =
      x L m hmL.symm (b / a) * w m L hmL (-1 : (Polynomial (ZMod p))ˣ) *
        k2PolyNagaoSigma_pair p m L hmL (b % a) (-a) := by
  rw [k2PolyNagaoSigma_pair_eq p m L hmL a b, k2PolyNagaoSigma_step, dif_neg ha]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_pair_of_ne

/-- **The section.**  `σ(v) = pair (v m) (v L)`. -/
noncomputable def k2PolyNagaoSigma_sigma (m L : I) (hmL : m ≠ L)
    (v : I → Polynomial (ZMod p)) : SteinbergGroup I (Polynomial (ZMod p)) :=
  k2PolyNagaoSigma_pair p m L hmL (v m) (v L)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_sigma

/-- `σ(e_L) = 1`. -/
theorem k2PolyNagaoSigma_sigma_unitVec (m L : I) (hmL : m ≠ L) :
    k2PolyNagaoSigma_sigma p m L hmL (unitVec L) = 1 := by
  rw [k2PolyNagaoSigma_sigma, unitVec_apply, unitVec_apply, if_neg hmL, if_pos rfl,
    k2PolyNagaoSigma_pair_zero, k2PolyNagaoSigma_tau, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoSigma_sigma_unitVec

end GroupApproximation.BooneHigman.Metabelian.ElemFP
