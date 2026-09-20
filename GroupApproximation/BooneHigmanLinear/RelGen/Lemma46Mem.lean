import GroupApproximation.BooneHigmanLinear.RelGen.Lemma46
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# L–S Lemma 4.6: membership forms, and 4.6(4) modulo `St̄(R, J)` (k2-poly H.L3)

Lane k2-hl3b. Consequences of `RelGen.Lemma46` in the form L–S use them (Prop 4.9, Cor 4.10,
§5), in type A.

* `comm_cElt_x_mem_xGroup`, `comm_cElt_x_mem_relKer`: for `β ≠ ±α` and `s t ∈ J`,
  `⁅c_α(s, t), x_β(ξ)⁆ ∈ St(Φ, J) ≤ St̄(R, J)`: every coefficient in 4.6 (1)–(3) is a multiple of
  `s t`.
* `cElt_col_of_mul_eq_zero`, `cElt_row_of_mul_eq_zero`: for distinct `p, q, r` and `s t = 0`,
  `c_pr(s, t) = c_qr(-s, t)⁻¹` and `c_pr(s, t) = c_pq(s, -t)⁻¹`. This is L–S 4.6(4) with all
  terms in `St(Φ, st R)` dropped. The proofs are two abstract group computations (`col_core`,
  `row_core`) fed with Steinberg relations: write `x_rp(t) = ⁅x_rq(t), x_qp(1)⁆`, respectively
  `x_pr(s) = ⁅x_pq(s), x_qr(1)⁆`, and use 4.6 in the `s t = 0` form for the conjugation left over.
* `cElt_col_mem`, `cElt_row_mem`: for `s t ∈ J`, `c_pr(s, t) · c_qr(-s, t)` and
  `c_pr(s, t) · c_pq(s, -t)` lie in `St̄(R, J)` (pass to `St_I(R/J)`).
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

section Membership

theorem x_mem_xGroup_of_mem {J : Ideal R} {p q : I} (hpq : p ≠ q) {a : R} (ha : a ∈ J) :
    x p q hpq a ∈ xGroup I J :=
  Subgroup.subset_closure ⟨p, q, hpq, a, ha, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_mem_xGroup_of_mem

/-- `St(Φ, J) ≤ St̄(R, J)`. -/
theorem xGroup_le_relKer (J : Ideal R) : xGroup I J ≤ relKer I J := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨i, j, hij, s, hs, rfl⟩
  exact mem_relKer_iff_ringMap.mpr (by
    rw [ringMap_x, Ideal.Quotient.eq_zero_iff_mem.mpr hs, x_zero])

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.xGroup_le_relKer

/-- **L–S 4.6 (1)–(3)**, membership form: for `β = (k, l) ≠ ±(i, j)` and `s t ∈ J`,
`⁅c_ij(s, t), x_kl(ξ)⁆ ∈ St(Φ, J)`. -/
theorem comm_cElt_x_mem_xGroup {J : Ideal R} {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l)
    (h₁ : ¬(k = i ∧ l = j)) (h₂ : ¬(k = j ∧ l = i)) {s t : R} (hst : s * t ∈ J) (ξ : R) :
    ⁅cElt i j hij s t, x k l hkl ξ⁆ ∈ xGroup I J := by
  have hJ : ∀ r : R, s * t * r ∈ J := fun r => Ideal.mul_mem_right r J hst
  by_cases hki : k = i
  · have hlj : l ≠ j := fun h => h₁ ⟨hki, h⟩
    subst hki
    rw [comm_cElt_x_il hij hkl hlj.symm s t ξ]
    refine (xGroup I J).mul_mem (x_mem_xGroup_of_mem _ ?_) (x_mem_xGroup_of_mem _ ?_)
    · rw [show s * t ^ 2 * ξ = s * t * (t * ξ) by ring]; exact hJ _
    · rw [show s * t * ξ + s ^ 2 * t ^ 2 * ξ = s * t * (ξ + s * t * ξ) by ring]; exact hJ _
  by_cases hkj : k = j
  · have hli : l ≠ i := fun h => h₂ ⟨hkj, h⟩
    subst hkj
    rw [comm_cElt_x_jl hij hli.symm hkl s t ξ]
    refine (xGroup I J).mul_mem (x_mem_xGroup_of_mem _ ?_) (x_mem_xGroup_of_mem _ ?_)
    · exact neg_mem (hJ ξ)
    · rw [show s ^ 2 * t * ξ = s * t * (s * ξ) by ring]; exact neg_mem (hJ _)
  by_cases hli : l = i
  · subst hli
    rw [comm_cElt_x_ki hij hki hkj s t ξ]
    refine (xGroup I J).mul_mem (x_mem_xGroup_of_mem _ ?_) (x_mem_xGroup_of_mem _ ?_)
    · exact neg_mem (hJ ξ)
    · rw [show s ^ 2 * t * ξ = s * t * (s * ξ) by ring]; exact hJ _
  by_cases hlj : l = j
  · subst hlj
    rw [comm_cElt_x_kj hij hki hkj s t ξ]
    refine (xGroup I J).mul_mem (x_mem_xGroup_of_mem _ ?_) (x_mem_xGroup_of_mem _ ?_)
    · rw [show s * t ^ 2 * ξ = s * t * (t * ξ) by ring]; exact neg_mem (hJ _)
    · rw [show s * t * ξ + s ^ 2 * t ^ 2 * ξ = s * t * (ξ + s * t * ξ) by ring]; exact hJ _
  rw [comm_cElt_x_disj hij hkl hki hkj hli hlj]
  exact (xGroup I J).one_mem

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_mem_xGroup

/-- **L–S 4.6 (1)–(3)** in `St̄(R, J)`. -/
theorem comm_cElt_x_mem_relKer {J : Ideal R} {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l)
    (h₁ : ¬(k = i ∧ l = j)) (h₂ : ¬(k = j ∧ l = i)) {s t : R} (hst : s * t ∈ J) (ξ : R) :
    ⁅cElt i j hij s t, x k l hkl ξ⁆ ∈ relKer I J :=
  xGroup_le_relKer J (comm_cElt_x_mem_xGroup hij hkl h₁ h₂ hst ξ)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.comm_cElt_x_mem_relKer

end Membership

section ZeroProduct

/-- `s t = 0`: `c_ij(s, t)` commutes with `x_il(ξ)`. -/
theorem commute_cElt_x_il_of_mul_eq_zero {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {s t : R} (hst : s * t = 0) (ξ : R) : Commute (cElt i j hij s t) (x i l hil ξ) := by
  have h := comm_cElt_x_il hij hil hjl s t ξ
  rw [show s * t ^ 2 * ξ = 0 by linear_combination (t * ξ) * hst,
    show s * t * ξ + s ^ 2 * t ^ 2 * ξ = 0 by linear_combination (ξ + s * t * ξ) * hst,
    x_zero, x_zero, mul_one] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_cElt_x_il_of_mul_eq_zero

/-- `s t = 0`: `c_ij(s, t)` commutes with `x_jl(ξ)`. -/
theorem commute_cElt_x_jl_of_mul_eq_zero {i j l : I} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    {s t : R} (hst : s * t = 0) (ξ : R) : Commute (cElt i j hij s t) (x j l hjl ξ) := by
  have h := comm_cElt_x_jl hij hil hjl s t ξ
  rw [show -(s * t * ξ) = 0 by linear_combination (-ξ) * hst,
    show -(s ^ 2 * t * ξ) = 0 by linear_combination (-(s * ξ)) * hst,
    x_zero, x_zero, mul_one] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_cElt_x_jl_of_mul_eq_zero

/-- The group computation behind `cElt_col_of_mul_eq_zero`. -/
theorem col_core {G : Type*} [Group G] {P W Y Z E D : G} (hW : W = Y * Z * Y⁻¹ * Z⁻¹)
    (hPY : P * Y = Y * P) (hPZ : P * Z * P⁻¹ = E⁻¹ * Z) (hEZ : E * Z = Z * E)
    (hD : D = E⁻¹ * Y⁻¹ * E * Y) (hDZ : D * Z = Z * D) :
    P * W * P⁻¹ * W⁻¹ = Y * E⁻¹ * Y⁻¹ * E := by
  have hPY' : P * Y * P⁻¹ = Y := by rw [hPY, mul_inv_cancel_right]
  have hPYi : P * Y⁻¹ * P⁻¹ = Y⁻¹ := by
    rw [show P * Y⁻¹ * P⁻¹ = (P * Y * P⁻¹)⁻¹ by group, hPY']
  have hPZi : P * Z⁻¹ * P⁻¹ = (E⁻¹ * Z)⁻¹ := by
    rw [show P * Z⁻¹ * P⁻¹ = (P * Z * P⁻¹)⁻¹ by group, hPZ]
  have hconj : P * W * P⁻¹ =
      P * Y * P⁻¹ * (P * Z * P⁻¹) * (P * Y⁻¹ * P⁻¹) * (P * Z⁻¹ * P⁻¹) := by
    rw [hW]; group
  have hE : E = Z * E * Z⁻¹ := by rw [← hEZ, mul_inv_cancel_right]
  have hZD : Z * D * Z⁻¹ = D := by rw [← hDZ, mul_inv_cancel_right]
  rw [hconj, hPY', hPZ, hPYi, hPZi, hW]
  calc Y * (E⁻¹ * Z) * Y⁻¹ * (E⁻¹ * Z)⁻¹ * (Y * Z * Y⁻¹ * Z⁻¹)⁻¹
      = Y * ((Z * E * Z⁻¹)⁻¹ * Z) * Y⁻¹ * ((Z * E * Z⁻¹)⁻¹ * Z)⁻¹ *
          (Y * Z * Y⁻¹ * Z⁻¹)⁻¹ := by rw [← hE]
    _ = Y * (Z * D * Z⁻¹) * Y⁻¹ := by rw [hD]; group
    _ = Y * D * Y⁻¹ := by rw [hZD]
    _ = Y * E⁻¹ * Y⁻¹ * E := by rw [hD]; group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.col_core

/-- The group computation behind `cElt_row_of_mul_eq_zero`. -/
theorem row_core {G : Type*} [Group G] {X w u v y d : G} (hX : X = u * v * u⁻¹ * v⁻¹)
    (hwu : w * u = u * w) (hwv : w * v * w⁻¹ = y⁻¹ * v) (hyv : y * v = v * y)
    (hd : d = u⁻¹ * y⁻¹ * u * y) (hvd : v * d = d * v) :
    X * w * X⁻¹ * w⁻¹ = y⁻¹ * u * y * u⁻¹ := by
  have hwu' : w * u * w⁻¹ = u := by rw [hwu, mul_inv_cancel_right]
  have hwui : w * u⁻¹ * w⁻¹ = u⁻¹ := by
    rw [show w * u⁻¹ * w⁻¹ = (w * u * w⁻¹)⁻¹ by group, hwu']
  have hwvi : w * v⁻¹ * w⁻¹ = (y⁻¹ * v)⁻¹ := by
    rw [show w * v⁻¹ * w⁻¹ = (w * v * w⁻¹)⁻¹ by group, hwv]
  have hconj : w * X * w⁻¹ =
      w * u * w⁻¹ * (w * v * w⁻¹) * (w * u⁻¹ * w⁻¹) * (w * v⁻¹ * w⁻¹) := by
    rw [hX]; group
  have hy : y = v * y * v⁻¹ := by rw [← hyv, mul_inv_cancel_right]
  have hvd' : v * d * v⁻¹ = d := by rw [hvd, mul_inv_cancel_right]
  calc X * w * X⁻¹ * w⁻¹ = X * (w * X * w⁻¹)⁻¹ := by group
    _ = u * v * u⁻¹ * v⁻¹ * (u * (y⁻¹ * v) * u⁻¹ * (y⁻¹ * v)⁻¹)⁻¹ := by
        rw [hconj, hwu', hwv, hwui, hwvi, hX]
    _ = u * v * u⁻¹ * v⁻¹ *
          (u * ((v * y * v⁻¹)⁻¹ * v) * u⁻¹ * ((v * y * v⁻¹)⁻¹ * v)⁻¹)⁻¹ := by rw [← hy]
    _ = u * (v * d * v⁻¹) * u⁻¹ := by rw [hd]; group
    _ = u * d * u⁻¹ := by rw [hvd']
    _ = y⁻¹ * u * y * u⁻¹ := by rw [hd]; group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.row_core

/-- **L–S 4.6(4)**, `s t = 0`: `c_pr(s, t) = c_qr(-s, t)⁻¹`. -/
theorem cElt_col_of_mul_eq_zero {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {s t : R} (hst : s * t = 0) : cElt p r hpr s t = (cElt q r hqr (-s) t)⁻¹ := by
  have hW : x r p hpr.symm t = x r q hqr.symm t * x q p hpq.symm 1 * (x r q hqr.symm t)⁻¹ *
      (x q p hpq.symm 1)⁻¹ := by
    rw [← commutatorElement_def, x_commutator r q p hqr.symm hpq.symm hpr.symm t 1, mul_one]
  have hPY : x p r hpr s * x r q hqr.symm t = x r q hqr.symm t * x p r hpr s :=
    commutatorElement_eq_one_iff_mul_comm.mp (by
      rw [x_commutator p r q hpr hqr.symm hpq s t, hst, x_zero])
  have hPZ : x p r hpr s * x q p hpq.symm 1 * (x p r hpr s)⁻¹ =
      (x q r hqr s)⁻¹ * x q p hpq.symm 1 := by
    rw [x_conj_rev hpq.symm hpr hqr 1 s, one_mul, x_neg]
  have hEZ : x q r hqr s * x q p hpq.symm 1 = x q p hpq.symm 1 * x q r hqr s :=
    (x_commute_of_ne q r q p hqr hpq.symm hqr.symm hpq s 1).eq
  have hD : cElt q r hqr (-s) (-t) =
      (x q r hqr s)⁻¹ * (x r q hqr.symm t)⁻¹ * x q r hqr s * x r q hqr.symm t := by
    simp only [cElt, commutatorElement_def, x_neg, inv_inv]
  have hDZ : cElt q r hqr (-s) (-t) * x q p hpq.symm 1 =
      x q p hpq.symm 1 * cElt q r hqr (-s) (-t) :=
    (commute_cElt_x_il_of_mul_eq_zero hqr hpq.symm hpr.symm
      ((neg_mul_neg s t).trans hst) 1).eq
  rw [show cElt p r hpr s t = ⁅x p r hpr s, x r p hpr.symm t⁆ from rfl, commutatorElement_def,
    col_core hW hPY hPZ hEZ hD hDZ]
  simp only [cElt, commutatorElement_def, x_neg]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_col_of_mul_eq_zero

/-- **L–S 4.6(4)**, `s t = 0`: `c_pr(s, t) = c_pq(s, -t)⁻¹`. -/
theorem cElt_row_of_mul_eq_zero {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {s t : R} (hst : s * t = 0) : cElt p r hpr s t = (cElt p q hpq s (-t))⁻¹ := by
  have hX : x p r hpr s = x p q hpq s * x q r hqr 1 * (x p q hpq s)⁻¹ * (x q r hqr 1)⁻¹ := by
    rw [← commutatorElement_def, x_commutator p q r hpq hqr hpr s 1, mul_one]
  have hwu : x r p hpr.symm t * x p q hpq s = x p q hpq s * x r p hpr.symm t :=
    commutatorElement_eq_one_iff_mul_comm.mp (by
      rw [x_commutator r p q hpr.symm hpq hqr.symm t s, mul_comm t s, hst, x_zero])
  have hwv : x r p hpr.symm t * x q r hqr 1 * (x r p hpr.symm t)⁻¹ =
      (x q p hpq.symm t)⁻¹ * x q r hqr 1 := by
    rw [x_conj_rev hqr hpr.symm hpq.symm 1 t, one_mul, x_neg]
  have hyv : x q p hpq.symm t * x q r hqr 1 = x q r hqr 1 * x q p hpq.symm t :=
    (x_commute_of_ne q p q r hpq.symm hqr hpq hqr.symm t 1).eq
  have hd : cElt p q hpq (-s) (-t) =
      (x p q hpq s)⁻¹ * (x q p hpq.symm t)⁻¹ * x p q hpq s * x q p hpq.symm t := by
    simp only [cElt, commutatorElement_def, x_neg, inv_inv]
  have hvd : x q r hqr 1 * cElt p q hpq (-s) (-t) = cElt p q hpq (-s) (-t) * x q r hqr 1 :=
    (commute_cElt_x_jl_of_mul_eq_zero hpq hpr hqr ((neg_mul_neg s t).trans hst) 1).eq.symm
  rw [show cElt p r hpr s t = ⁅x p r hpr s, x r p hpr.symm t⁆ from rfl, commutatorElement_def,
    row_core hX hwu hwv hyv hd hvd]
  simp only [cElt, commutatorElement_def, x_neg]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_row_of_mul_eq_zero

end ZeroProduct

section Quotient

/-- Naturality of `c_ij(s, t)`. -/
theorem ringMap_cElt {S : Type*} [CommRing S] (f : R →+* S) (i j : I) (hij : i ≠ j) (s t : R) :
    ringMap f (cElt i j hij s t) = cElt i j hij (f s) (f t) := by
  simp only [cElt, map_commutatorElement, ringMap_x]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ringMap_cElt

theorem mk_mul_mk_eq_zero {J : Ideal R} {s t : R} (hst : s * t ∈ J) :
    Ideal.Quotient.mk J s * Ideal.Quotient.mk J t = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hst]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.mk_mul_mk_eq_zero

/-- **L–S 4.6(4)** modulo `St̄(R, J)`: `c_pr(s, t) · c_qr(-s, t) ∈ St̄(R, J)` for `s t ∈ J`. -/
theorem cElt_col_mem {J : Ideal R} {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {s t : R} (hst : s * t ∈ J) : cElt p r hpr s t * cElt q r hqr (-s) t ∈ relKer I J := by
  refine mem_relKer_iff_ringMap.mpr ?_
  rw [map_mul, ringMap_cElt, ringMap_cElt, map_neg,
    cElt_col_of_mul_eq_zero hpq hqr hpr (mk_mul_mk_eq_zero hst), inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_col_mem

/-- **L–S 4.6(4)** modulo `St̄(R, J)`: `c_pr(s, t) · c_pq(s, -t) ∈ St̄(R, J)` for `s t ∈ J`. -/
theorem cElt_row_mem {J : Ideal R} {p q r : I} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    {s t : R} (hst : s * t ∈ J) : cElt p r hpr s t * cElt p q hpq s (-t) ∈ relKer I J := by
  refine mem_relKer_iff_ringMap.mpr ?_
  rw [map_mul, ringMap_cElt, ringMap_cElt, map_neg,
    cElt_row_of_mul_eq_zero hpq hqr hpr (mk_mul_mk_eq_zero hst), inv_mul_cancel]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.cElt_row_mem

end Quotient

end GroupApproximation.BooneHigmanLinear.RelGen
