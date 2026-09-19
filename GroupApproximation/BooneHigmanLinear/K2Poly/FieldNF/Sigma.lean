import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.Check
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoSigmaLm
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: the explicit Euclidean section `σ` and its easy checks

k2-poly piece A5.2 (lane k2-field-a). This is lanes 92q's `ElemFPK2PolyNagaoSigmaDef` and
`ElemFPK2PolyNagaoSigmaLm` over an arbitrary field `F` instead of `ZMod p`. Notation of
`FieldNF.Check`. Fix two indices `m ≠ L` and put `W' = w_mL(-1)`, which acts on the
`(m, L)` coordinates by `(c, d) ↦ (-d, c)` (`k2PolyNagaoSigma_act_W`, already ring-generic).

* `fnSigma_tau b`: `1` if `b = 1`, `h_mL(b)⁻¹` if `b` is another unit, `1` otherwise.
* `fnSigma_pair` (well-founded recursion on `deg a`): `pair 0 b = τ(b)` and, for `a ≠ 0`,
  `pair a b = x_Lm(b / a) · W' · pair (b % a) (-a)`, the Euclidean algorithm on `(a, b)`.
* `fnSigma_sigma v = pair (v m) (v L)`, with `σ(e_L) = 1`.
* `fnSigma_check_Lm`: the coset check of every `x_Lm(f)`, `f ∈ F[X]`, with target `Z ⊔ Q`.
* `fnSigma_check_W_lt`: the check of `W'` at the vectors with `deg v m < deg v L`.

Nothing here uses `K₂(F) = 1` or the multiplicativity of the torus. The `F_p` proofs only used
Euclidean division in `F_p[X]`, the ring-generic conjugation `k2PolyDeg_h_conj_exists`, and
the Steinberg relations, so every check element that lay in `Q` still lies in `Q ≤ Z ⊔ Q`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV fnZ)
open GroupApproximation.BooneHigman.Metabelian.ElemFP (k2PolyDeg_h_conj_exists
  k2PolyNagaoSigma_act_W)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (x_mem_rootSpan act
  act_mul act_x_apply unitVec unitVec_apply)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (F : Type) [Field F]

open Classical in
/-- The base case of `σ`: `τ(1) = 1`, `τ(b) = h_mL(b)⁻¹` for a unit `b ≠ 1`, else `1`. -/
noncomputable def fnSigma_tau (m L : I) (hmL : m ≠ L) (b : Polynomial F) :
    SteinbergGroup I (Polynomial F) :=
  if b = 1 then 1 else if hb : IsUnit b then (h m L hmL hb.unit)⁻¹ else 1

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_tau

open Classical in
/-- One Euclidean step: `(a, b) ↦ x_Lm(b / a) · W' · rec (b % a) (-a)` for `a ≠ 0`. -/
noncomputable def fnSigma_step (m L : I) (hmL : m ≠ L) (a : Polynomial F)
    (rec : ∀ c : Polynomial F, c.degree < a.degree → Polynomial F →
      SteinbergGroup I (Polynomial F))
    (b : Polynomial F) : SteinbergGroup I (Polynomial F) :=
  if ha : a = 0 then fnSigma_tau F m L hmL b
  else x L m hmL.symm (b / a) * w m L hmL (-1 : (Polynomial F)ˣ) *
    rec (b % a) (Polynomial.degree_mod_lt b ha) (-a)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_step

/-- The Euclidean word of the column `(a, b)`, by well-founded recursion on `deg a`. -/
noncomputable def fnSigma_pair (m L : I) (hmL : m ≠ L) :
    Polynomial F → Polynomial F → SteinbergGroup I (Polynomial F) :=
  WellFounded.fix
    (C := fun _ => Polynomial F → SteinbergGroup I (Polynomial F))
    (Polynomial.degree_lt_wf (R := F)) (fnSigma_step F m L hmL)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_pair

/-- **The section.** `σ(v) = pair (v m) (v L)`. -/
noncomputable def fnSigma_sigma (m L : I) (hmL : m ≠ L) (v : I → Polynomial F) :
    SteinbergGroup I (Polynomial F) :=
  fnSigma_pair F m L hmL (v m) (v L)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_sigma

end Defs

variable {F : Type} [Field F]

/-- The unfolding equation of `fnSigma_pair`. -/
theorem fnSigma_pair_eq (m L : I) (hmL : m ≠ L) (a b : Polynomial F) :
    fnSigma_pair F m L hmL a b =
      fnSigma_step F m L hmL a (fun c _ => fnSigma_pair F m L hmL c) b :=
  congrFun (WellFounded.fix_eq
    (C := fun _ => Polynomial F → SteinbergGroup I (Polynomial F))
    (Polynomial.degree_lt_wf (R := F)) (fnSigma_step F m L hmL) a) b

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_pair_eq

/-- `pair 0 b = τ(b)`. -/
theorem fnSigma_pair_zero (m L : I) (hmL : m ≠ L) (b : Polynomial F) :
    fnSigma_pair F m L hmL 0 b = fnSigma_tau F m L hmL b := by
  rw [fnSigma_pair_eq m L hmL 0 b, fnSigma_step, dif_pos rfl]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_pair_zero

/-- `pair a b = x_Lm(b / a) · W' · pair (b % a) (-a)` for `a ≠ 0`. -/
theorem fnSigma_pair_of_ne (m L : I) (hmL : m ≠ L) {a : Polynomial F} (ha : a ≠ 0)
    (b : Polynomial F) :
    fnSigma_pair F m L hmL a b =
      x L m hmL.symm (b / a) * w m L hmL (-1 : (Polynomial F)ˣ) *
        fnSigma_pair F m L hmL (b % a) (-a) := by
  rw [fnSigma_pair_eq m L hmL a b, fnSigma_step, dif_neg ha]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_pair_of_ne

/-- `σ(e_L) = 1`. -/
theorem fnSigma_sigma_unitVec (m L : I) (hmL : m ≠ L) :
    fnSigma_sigma F m L hmL (unitVec L) = 1 := by
  rw [fnSigma_sigma, unitVec_apply, unitVec_apply, if_neg hmL, if_pos rfl,
    fnSigma_pair_zero, fnSigma_tau, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_sigma_unitVec

/-- `σ(e_L) = 1` lies in the target. -/
theorem fnSigma_sigma_unitVec_mem {K : Finset I} (m L : I) (hmL : m ≠ L) :
    fnSigma_sigma F m L hmL (unitVec L) ∈ fnZQ F K L := by
  rw [fnSigma_sigma_unitVec]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_sigma_unitVec_mem

/-- `(b + f a) % a = b % a`. -/
theorem fnSigma_mod_add (a b f : Polynomial F) : (b + f * a) % a = b % a := by
  have hz : f * a % a = 0 := EuclideanDomain.mod_eq_zero.2 (dvd_mul_left a f)
  rw [Polynomial.add_mod, hz, add_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_mod_add

/-- `(b + f a) / a = b / a + f` for `a ≠ 0`. -/
theorem fnSigma_div_add {a : Polynomial F} (ha : a ≠ 0) (b f : Polynomial F) :
    (b + f * a) / a = b / a + f := by
  have h1 : a * ((b + f * a) / a) + b % a = b + f * a := by
    rw [← fnSigma_mod_add a b f]
    exact EuclideanDomain.div_add_mod _ _
  have h2 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod _ _
  apply mul_left_cancel₀ ha
  linear_combination h1 - h2

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_div_add

/-- `Q ≤ Z ⊔ Q`. -/
theorem fn_mem_ZQ_of_mem_Q {K : Finset I} {L : I} {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnQ F K L) : g ∈ fnZQ F K L :=
  Subgroup.mem_sup_right hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_mem_ZQ_of_mem_Q

/-- Every `x_Lm(c)` (`m ∈ K`) lies in `Z ⊔ Q`. -/
theorem fnSigma_x_mem_ZQ {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (c : Polynomial F) : x L m hmL.symm c ∈ fnZQ F K L :=
  fn_mem_ZQ_of_mem_Q (Subgroup.mem_sup_right
    (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hmL.symm c ⟨rfl, hmK⟩))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_x_mem_ZQ

/-- `τ(b)⁻¹ x_Lm(f) τ(b) ∈ Z ⊔ Q`. -/
theorem fnSigma_tau_conj {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∃ n, m ≠ n ∧ L ≠ n) (b f : Polynomial F) :
    (fnSigma_tau F m L hmL b)⁻¹ * x L m hmL.symm f * fnSigma_tau F m L hmL b ∈
      fnZQ F K L := by
  by_cases hb1 : b = 1
  · rw [fnSigma_tau, if_pos hb1, inv_one, one_mul, mul_one]
    exact fnSigma_x_mem_ZQ hmL hmK f
  by_cases hbu : IsUnit b
  · rw [fnSigma_tau, if_neg hb1, dif_pos hbu, inv_inv]
    obtain ⟨c, hc⟩ := k2PolyDeg_h_conj_exists m L L m hmL hmL.symm hthird hbu.unit f
    rw [hc]
    exact fnSigma_x_mem_ZQ hmL hmK c
  · rw [fnSigma_tau, if_neg hb1, dif_neg hbu, inv_one, one_mul, mul_one]
    exact fnSigma_x_mem_ZQ hmL hmK f

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_tau_conj

/-- **The `x_Lm` family.** The coset check of every `x_Lm(f)`, `f ∈ F[X]`, against `σ`. -/
theorem fnSigma_check_Lm {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∃ n, m ≠ n ∧ L ≠ n) (f : Polynomial F) :
    fnCheck F K L (fnSigma_sigma F m L hmL) (x L m hmL.symm f) := by
  intro v _
  have e1 : act (x L m hmL.symm f) v m = v m := by
    rw [act_x_apply, if_neg hmL, add_zero]
  have e2 : act (x L m hmL.symm f) v L = v L + f * v m := by
    rw [act_x_apply, if_pos rfl]
  rw [fnSigma_sigma, fnSigma_sigma, e1, e2]
  by_cases ha : v m = 0
  · rw [ha, mul_zero, add_zero, fnSigma_pair_zero]
    exact fnSigma_tau_conj hmL hmK hthird (v L) f
  have e : ∀ A B C D : SteinbergGroup I (Polynomial F),
      (A * B * C * D)⁻¹ * A * (B * C * D) = 1 := fun A B C D => by group
  rw [fnSigma_pair_of_ne m L hmL ha, fnSigma_pair_of_ne m L hmL ha,
    fnSigma_mod_add, fnSigma_div_add ha, add_comm (v L / v m) f, ← x_mul, e]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_check_Lm

/-- **The easy half of the Weyl check.** If `deg v m < deg v L` then `σ(W' v) = W' σ(v)`, so
the check element of `W' = w_mL(-1)` at `v` is `1`. -/
theorem fnSigma_check_W_lt {K : Finset I} {m L : I} (hmL : m ≠ L)
    (v : I → Polynomial F) (hd : (v m).degree < (v L).degree) :
    (fnSigma_sigma F m L hmL (act (w m L hmL (-1 : (Polynomial F)ˣ)) v))⁻¹ *
        w m L hmL (-1 : (Polynomial F)ˣ) * fnSigma_sigma F m L hmL v ∈ fnZQ F K L := by
  obtain ⟨e1, e2⟩ := k2PolyNagaoSigma_act_W hmL v
  have hb : -(v L) ≠ 0 := neg_ne_zero.2 (Polynomial.ne_zero_of_degree_gt hd)
  have hdeg : (v m).degree < (-(v L)).degree := by
    rw [Polynomial.degree_neg]
    exact hd
  have e : ∀ A B : SteinbergGroup I (Polynomial F), (A * B)⁻¹ * A * B = 1 :=
    fun A B => by group
  rw [fnSigma_sigma, fnSigma_sigma, e1, e2,
    fnSigma_pair_of_ne m L hmL hb (v m), (Polynomial.div_eq_zero_iff hb).2 hdeg,
    (Polynomial.mod_eq_self_iff hb).2 hdeg, neg_neg, x_zero, one_mul, e]
  exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnSigma_check_W_lt

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
