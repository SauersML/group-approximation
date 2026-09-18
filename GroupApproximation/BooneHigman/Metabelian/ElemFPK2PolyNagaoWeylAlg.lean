import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoSigmaLm
import GroupApproximation.Meta.AxiomGuard

/-!
# The Weyl check of `σ`, part 1: Euclidean-division algebra and the orbit invariant

Lane `bh-met-93d`.  Polynomial algebra used by the Weyl check of the Euclidean section
`σ = k2PolyNagaoSigma_sigma` (`ElemFPK2PolyNagaoSigmaDef`):

* `k2PolyNagaoWeyl_divmod_unique`: uniqueness of Euclidean division in `F_p[X]`;
* the effect of signs and unit scalings on `/` and `%`;
* `k2PolyNagaoWeyl_coprime_act`: for `K = {m}`, every element of `G_{K ∪ {L}}(F_p[X])`
  preserves coprimality of the `(m, L)` coordinates; hence every vector of the orbit of `e_L`
  has coprime `(m, L)` coordinates (`k2PolyNagaoWeyl_coprime_orbit`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan_induction
  act act_mul act_one act_x_apply unitVec unitVec_apply)

/-- Coprimality passes along an invertible-looking change of generators. -/
theorem k2PolyNagaoWeyl_isCoprime_of_comb {R : Type*} [CommRing R] {a b c d x1 y1 x2 y2 : R}
    (h : IsCoprime a b) (ha : a = x1 * c + y1 * d) (hb : b = x2 * c + y2 * d) :
    IsCoprime c d := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u * x1 + v * x2, u * y1 + v * y2, by linear_combination huv - u * ha - v * hb⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_isCoprime_of_comb

variable {p : ℕ} [Fact p.Prime]

/-- Uniqueness of Euclidean division: `b = a q + r`, `deg r < deg a` force `b / a = q` and
`b % a = r`. -/
theorem k2PolyNagaoWeyl_divmod_unique {a b q r : Polynomial (ZMod p)} (ha : a ≠ 0)
    (h : b = a * q + r) (hr : r.degree < a.degree) : b / a = q ∧ b % a = r := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  have hq : b / a = q := by
    by_contra hne
    have e : a * (b / a - q) = r - b % a := by linear_combination h1 + h
    have hd : a.degree ≤ (r - b % a).degree := by
      rw [← e]
      exact Polynomial.degree_le_mul_left a (sub_ne_zero.2 hne)
    have hlt : (r - b % a).degree < a.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr (Polynomial.degree_mod_lt b ha))
    exact absurd hd (not_le.2 hlt)
  refine ⟨hq, ?_⟩
  rw [hq] at h1
  linear_combination h1 + h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_divmod_unique

/-- `a / (-b) = -(a / b)` and `a % (-b) = a % b`. -/
theorem k2PolyNagaoWeyl_divmod_neg_right (a : Polynomial (ZMod p)) {b : Polynomial (ZMod p)}
    (hb : b ≠ 0) : a / -b = -(a / b) ∧ a % -b = a % b := by
  have h1 : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b
  refine k2PolyNagaoWeyl_divmod_unique (neg_ne_zero.2 hb) (by linear_combination -h1) ?_
  rw [Polynomial.degree_neg]
  exact Polynomial.degree_mod_lt a hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_divmod_neg_right

/-- `(-a) / b = -(a / b)` and `(-a) % b = -(a % b)`. -/
theorem k2PolyNagaoWeyl_divmod_neg_left (a : Polynomial (ZMod p)) {b : Polynomial (ZMod p)}
    (hb : b ≠ 0) : -a / b = -(a / b) ∧ -a % b = -(a % b) := by
  have h1 : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b
  refine k2PolyNagaoWeyl_divmod_unique hb (by linear_combination h1) ?_
  rw [Polynomial.degree_neg]
  exact Polynomial.degree_mod_lt a hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_divmod_neg_left

/-- Scaling the column `(a, b)` to `(δ a, δ⁻¹ b)` by a constant unit `δ`. -/
theorem k2PolyNagaoWeyl_divmod_scale (δ : (ZMod p)ˣ) {a : Polynomial (ZMod p)} (ha : a ≠ 0)
    (b : Polynomial (ZMod p)) :
    (Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * b) / (Polynomial.C (δ : ZMod p) * a) =
        Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) *
          Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * (b / a) ∧
      (Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * b) % (Polynomial.C (δ : ZMod p) * a) =
        Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * (b % a) := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  have hu : Polynomial.C (δ : ZMod p) * Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ha' : Polynomial.C (δ : ZMod p) * a ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.2 δ.ne_zero) ha
  refine k2PolyNagaoWeyl_divmod_unique ha' (by
    linear_combination -Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * h1 -
      Polynomial.C ((δ⁻¹ : (ZMod p)ˣ) : ZMod p) * a * (b / a) * hu) ?_
  rw [Polynomial.degree_C_mul δ⁻¹.ne_zero, Polynomial.degree_C_mul δ.ne_zero]
  exact Polynomial.degree_mod_lt b ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_divmod_scale

/-- One Euclidean step keeps a coprime column coprime: `(a, b)` to `(b % a, -a)`. -/
theorem k2PolyNagaoWeyl_coprime_step {a b : Polynomial (ZMod p)} (h : IsCoprime a b) :
    IsCoprime (b % a) (-a) := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  exact k2PolyNagaoWeyl_isCoprime_of_comb h (x1 := 0) (y1 := -1) (x2 := 1) (y2 := -(b / a))
    (by ring) (by linear_combination -h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_coprime_step

variable {I : Type} [Fintype I] [DecidableEq I]

/-- For `K = {m}`, every element of `G_{K ∪ {L}}(F_p[X])` preserves coprimality of the
`(m, L)` coordinates. -/
theorem k2PolyNagaoWeyl_coprime_act {K : Finset I} {m L : I} (hmL : m ≠ L)
    (hKm : ∀ i ∈ K, i = m) {y : SteinbergGroup I (Polynomial (ZMod p))}
    (hy : y ∈ k2PolyDeg_G p K L) :
    ∀ v : I → Polynomial (ZMod p), IsCoprime (v m) (v L) →
      IsCoprime (act y v m) (act y v L) := by
  unfold k2PolyDeg_G at hy
  refine rootSpan_induction (Q := fun y => ∀ v : I → Polynomial (ZMod p),
    IsCoprime (v m) (v L) → IsCoprime (act y v m) (act y v L)) ?_ ?_ ?_ hy
  · intro i j hij a hq v hv
    have hi : i = L ∨ i = m := (Finset.mem_insert.1 hq.1).imp id (hKm i)
    have hj : j = L ∨ j = m := (Finset.mem_insert.1 hq.2).imp id (hKm j)
    rw [act_x_apply, act_x_apply]
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · rw [if_neg (fun h => hmL (h.trans hi)), if_pos hi.symm, hj, add_zero]
      exact k2PolyNagaoWeyl_isCoprime_of_comb hv (x1 := 1) (y1 := 0) (x2 := -a) (y2 := 1)
        (by ring) (by ring)
    · rw [if_pos hi.symm, if_neg (fun h => hmL (h.trans hi).symm), hj, add_zero]
      exact k2PolyNagaoWeyl_isCoprime_of_comb hv (x1 := 1) (y1 := -a) (x2 := 0) (y2 := 1)
        (by ring) (by ring)
    · exact absurd (hi.trans hj.symm) hij
  · intro v hv
    rw [act_one]
    exact hv
  · intro g k _ _ hg hk v hv
    rw [act_mul]
    exact hg _ (hk v hv)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_coprime_act

/-- Every vector of the `G_{K ∪ {L}}`-orbit of `e_L` (`K = {m}`) has coprime `(m, L)`
coordinates. -/
theorem k2PolyNagaoWeyl_coprime_orbit {K : Finset I} {m L : I} (hmL : m ≠ L)
    (hKm : ∀ i ∈ K, i = m) {v : I → Polynomial (ZMod p)}
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) : IsCoprime (v m) (v L) := by
  obtain ⟨y, hy, rfl⟩ := hv
  refine k2PolyNagaoWeyl_coprime_act hmL hKm hy (unitVec L) ?_
  rw [unitVec_apply, unitVec_apply, if_neg hmL, if_pos rfl]
  exact isCoprime_one_right

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWeyl_coprime_orbit

end GroupApproximation.BooneHigman.Metabelian.ElemFP
